(* based on riscv.Platform.Minimal *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Export riscv.Platform.RiscvMachine.
Require Export Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import ListNotations.

Module device.
  (* a deterministic device *)
  Class device{word: word.word 32} := {
    state: Type;
    reset_state: state;
    run1: state -> state;
    addr_range_start: word;
    addr_range_pastend: word;
    readReq(num_bytes: nat)(addr: word): state -> state;
    readResp: state -> option word;
    writeReq(num_bytes: nat)(addr value: word): state -> state;
    writeResp: state -> option unit;
    maxRespDelay: nat;
  }.
End device.
Notation device := device.device.
Global Coercion device.state: device >-> Sortclass.

(* Needed because of https://github.com/coq/coq/issues/14031 *)
#[export] Hint Extern 1 (MachineWidth _) => exact MkMachineWidth.MachineWidth_XLEN
  : typeclass_instances.

(* TODO move to coqutil *)
Module word. Section WithParams.
  Context {width: Z} {word: word.word width}.
  Definition leu(a b: word) := negb (word.gtu a b).
  Definition geu(a b: word) := negb (word.ltu a b).
End WithParams. End word.

Section WithParams.
  Context {word: Interface.word.word 32}.
  Context {word_ok: word.ok word}.

  Global Instance mkWords: Words := {|
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  |}.

  Context {D: device}.
  Context {mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  (* redefine monad notations with explicit type in Bind, otherwise Coq might will
     infer the wrong instance in loadN, without backtracking enough *)
  Notation "x <- m1 ; m2" := (Bind (M := OState (ExtraRiscvMachine D)) m1 (fun x => m2))
    (right associativity, at level 60).
  Notation "m1 ;; m2" := (Bind (M := OState (ExtraRiscvMachine D)) m1 (fun _ => m2))
    (right associativity, at level 60).

  Definition update(f: ExtraRiscvMachine D -> ExtraRiscvMachine D):
    OState (ExtraRiscvMachine D) unit :=
    m <- get; put (f m).

  Definition updateExtra(f: D -> D): OState (ExtraRiscvMachine D) unit :=
    update (fun m => withExtraState (f m.(getExtraState)) m).

  Definition fail_if_None{R}(o: option R): OState (ExtraRiscvMachine D) R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Definition waitFor{T: Type}(resp: D -> option T): nat -> OState (ExtraRiscvMachine D) T :=
    fix rec fuel :=
      mach <- get;
      match resp mach.(getExtraState) with
      | Some t => Return t
      | None => match fuel with
                | O => fail_hard
                | S fuel' => updateExtra device.run1;; rec fuel'
                end
      end.

  Definition mmioLoad(n: nat)(addr: word): OState (ExtraRiscvMachine D) (HList.tuple byte n) :=
    updateExtra (device.readReq n addr);;
    v <- waitFor device.readResp device.maxRespDelay;
    Return (LittleEndian.split n (word.unsigned v)).

  Definition mmioStore(n: nat)(addr: word)(v: HList.tuple byte n): OState (ExtraRiscvMachine D) unit :=
    updateExtra (device.writeReq n addr (word.of_Z (LittleEndian.combine n v)));;
    waitFor device.writeResp device.maxRespDelay.

  Definition loadN(n: nat)(kind: SourceType)(a: word):
    OState (ExtraRiscvMachine D) (HList.tuple byte n) :=
    mach <- get;
    match Memory.load_bytes n mach.(getMachine).(getMem) a with
    | Some v =>
      match kind with
      | Fetch => if isXAddr4B a mach.(getMachine).(getXAddrs) then Return v else fail_hard
      | _ => Return v
      end
    | None => if word.leu device.addr_range_start a
                 && word.leu (word.add a (word.of_Z (Z.of_nat n))) device.addr_range_pastend
              then mmioLoad n a
              else fail_hard
    end.

  Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n) :=
    mach <- get;
    match Memory.store_bytes n mach.(getMachine).(getMem) a v with
    | Some m => update (withMem m)
    | None => if word.leu device.addr_range_start a
                 && word.leu (word.add a (word.of_Z (Z.of_nat n))) device.addr_range_pastend
              then mmioStore n a v
              else fail_hard
    end;;
    update (fun mach => withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) mach).

  Global Instance IsRiscvMachine: RiscvProgram (OState (ExtraRiscvMachine D)) word := {
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            match map.get mach.(getMachine).(getRegs) reg with
            | Some v => Return v
            | None => Return (word.of_Z 0)
            end
          else
            fail_hard;

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          if (0 <? reg) && (reg <? 32) then
            update (fun mach => withRegs (map.put mach.(getMachine).(getRegs) reg v) mach)
          else
            fail_hard;

      getPC := mach <- get; Return mach.(getMachine).(getPc);

      setPC newPC := update (withNextPc newPC);

      loadByte   := loadN 1;
      loadHalf   := loadN 2;
      loadWord   := loadN 4;
      loadDouble := loadN 8;

      storeByte   := storeN 1;
      storeHalf   := storeN 2;
      storeWord   := storeN 4;
      storeDouble := storeN 8;

      makeReservation  addr := fail_hard;
      clearReservation addr := fail_hard;
      checkReservation addr := fail_hard;
      getCSRField f := fail_hard;
      setCSRField f v := fail_hard;
      getPrivMode := fail_hard;
      setPrivMode v := fail_hard;
      fence _ _ := fail_hard;

      endCycleNormal := update (fun m => (withPc m.(getNextPc)
                                         (withNextPc (word.add m.(getNextPc) (word.of_Z 4)) m)));

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      endCycleEarly{A: Type} := fail_hard;
  }.

  Fixpoint device_steps(n: nat): OState (ExtraRiscvMachine D) unit :=
    match n with
    | O => Return tt
    | S n' => updateExtra device.run1;; device_steps n'
    end.

  (* In the time that the riscv core needs to execute the i-th instruction, how many
     cycles does the device execute? *)
  Definition schedule := nat -> nat.

  Section WithSchedule.
    Context (sched: schedule).

    Definition nth_step(n: nat): OState (ExtraRiscvMachine D) unit :=
      device_steps (sched n);; Run.run1 RV32I.

    Fixpoint run(nsteps: nat): OState (ExtraRiscvMachine D) unit :=
      match nsteps with
      | O => Return tt
      | S n => run n;; nth_step n
      end.
  End WithSchedule.

End WithParams.
