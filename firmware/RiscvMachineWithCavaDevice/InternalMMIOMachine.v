(* A deterministic RiscvMachine performing only internal MMIO,
   i.e. MMIO between the processor and a hardware device simulator that
   does not show up in the event trace.
   No external MMIO (ie interaction with the external world) is performed
   by this machine, so mach.(getMachine).(getLog) always remains [].
   Based on riscv.Platform.Minimal *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Primitives.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MaterializeRiscvProgram.
Require Export Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Bitwidth32.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import ListNotations.

(* TODO move to riscv-coq *)
Module free.
  Section WithParams.
    Context {action: Type} {result: action -> Type} {state: Type}
            (interp_action: forall a: action, OState state (result a)) {answer: Type}.
    Definition interp_as_OState_body interp_as_OState (m: free action result answer):
      OState state answer :=
      match m with
      | free.ret x => Return x
      | free.act a k => Bind (interp_action a) (fun r => interp_as_OState (k r))
      end.
    Fixpoint interp_as_OState(m: free action result answer): OState state answer :=
      interp_as_OState_body interp_as_OState m.
  End WithParams.
End free.

Module device.
  (* A deterministic device, to be instantiated with a Cava device *)
  Class device := {
    (* circuit state, will be instantiated with result of Cava.Core.Circuit.circuit_state *)
    state: Type;

    (* tells whether the device is in a state where it's ready to be used, typically
       includes Cava.Core.Circuit.reset_state *)
    is_ready_state: state -> Prop;

    (* run one simulation step, will be instantiated with Cava.Semantics.Combinational.step *)
    run1: (* input: current state, is_read_req, is_write_req, req_addr, req_value *)
      state -> bool * bool * Bvector 32 * Bvector 32 ->
      (* output: next state, is_resp, resp *)
      state * (bool * Bvector 32);

    (* lowest address of the MMIO address range used to communicate with this device *)
    addr_range_start: Z;

    (* one past the highest MMIO address *)
    addr_range_pastend: Z;

    (* max number of device cycles (ie calls of run1) this device takes to serve read/write requests *)
    maxRespDelay: nat;
  }.
  (* Note: there are two levels of "polling until a response is available":
     - on the hardware level, using readResp/writeResp, which appears as
       blocking I/O for the software
     - on the software level, using MMIO reads on some status register,
       where the MMIO read immediately gives a "busy" response, and the
       software keeps polling until the MMIO read returns a "done" response *)

  (* returning None means out of fuel and must not happen if fuel >= device.maxRespDelay *)
  Definition runUntilResp{D: device}(is_read_req is_write_req: bool)(req_addr req_value: Bvector 32) :=
    fix rec(fuel: nat)(s: device.state): option (Bvector 32) * device.state :=
      let '(next, (is_resp, resp)) := device.run1 s (is_read_req, is_write_req, req_addr, req_value) in
      if is_resp then (Some resp, next) else
        match fuel with
        | O => (None, next)
        | S fuel' => rec fuel' next
        end.

  Section WithWordAndDevice.
    Context {word: Interface.word.word 32} {word_ok: word.ok word} {D: device}.

    Definition isMMIOAddr(a: word): Prop :=
      device.addr_range_start <= word.unsigned a < device.addr_range_pastend.

    Definition isMMIOAddrB(a: word)(n: nat): bool :=
      (device.addr_range_start <=? word.unsigned a) &&
      (word.unsigned a + Z.of_nat n <=? device.addr_range_pastend).
  End WithWordAndDevice.
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

  Definition bv_to_word(v: Bvector 32): word :=
    word.of_Z (Z.of_N (Ndigits.Bv2N v)).

  Definition word_to_bv(w: word): Bvector 32 :=
    Ndigits.N2Bv_sized 32 (Z.to_N (word.unsigned w)).

  Definition runUntilResp(is_read_req is_write_req: bool)(req_addr req_value: word):
    OState (ExtraRiscvMachine D) word :=
    let req_addr := word_to_bv req_addr in
    let req_value := word_to_bv req_value in
    mach <- get;
    let (respo, new_device_state) := device.runUntilResp is_read_req is_write_req req_addr req_value
                                       device.maxRespDelay mach.(getExtraState) in
    put (withExtraState new_device_state mach);;
    resp <- fail_if_None respo;
    Return (bv_to_word resp).

  Definition mmioLoad(n: nat)(addr: word): OState (ExtraRiscvMachine D) (HList.tuple byte n) :=
    v <- runUntilResp true false addr (word.of_Z 0);
    Return (LittleEndian.split n (word.unsigned v)).

  Definition mmioStore(n: nat)(addr: word)(v: HList.tuple byte n): OState (ExtraRiscvMachine D) unit :=
    ignored <- runUntilResp false true addr (word.of_Z (LittleEndian.combine n v));
    Return tt.

  Definition loadN(n: nat)(kind: SourceType)(a: word):
    OState (ExtraRiscvMachine D) (HList.tuple byte n) :=
    mach <- get;
    match Memory.load_bytes n mach.(getMachine).(getMem) a with
    | Some v =>
      match kind with
      | Fetch => if isXAddr4B a mach.(getMachine).(getXAddrs) then Return v else fail_hard
      | _ => Return v
      end
    | None => if device.isMMIOAddrB a n then mmioLoad n a else fail_hard
    end.

  Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n) :=
    mach <- get;
    match Memory.store_bytes n mach.(getMachine).(getMem) a v with
    | Some m => update (withMem m)
    | None => if device.isMMIOAddrB a n then mmioStore n a v else fail_hard
    end;;
    update (fun mach => withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) mach).

  Definition interpret_action(a: riscv_primitive): OState (ExtraRiscvMachine D) (primitive_result a) :=
    match a with
    | GetRegister reg =>
        if Z.eq_dec reg Register0 then
          Return (word.of_Z 0)
        else
          mach <- get;
          match map.get mach.(getMachine).(getRegs) reg with
          | Some v => Return v
          | None => Return (word.of_Z 0)
          end
    | SetRegister reg v =>
        if Z.eq_dec reg Register0 then
          Return tt
        else
          update (fun mach => withRegs (map.put mach.(getMachine).(getRegs) reg v) mach)
    | GetPC => mach <- get; Return mach.(getMachine).(getPc)
    | SetPC newPC => update (withNextPc newPC)
    | LoadByte ctxid a => loadN 1 ctxid a
    | LoadHalf ctxid a => loadN 2 ctxid a
    | LoadWord ctxid a => loadN 4 ctxid a
    | LoadDouble ctxid a => loadN 8 ctxid a
    | StoreByte ctxid a v => storeN 1 ctxid a v
    | StoreHalf ctxid a v => storeN 2 ctxid a v
    | StoreWord ctxid a v => storeN 4 ctxid a v
    | StoreDouble ctxid a v => storeN 8 ctxid a v
    | EndCycleNormal => update (fun m => (withPc m.(getNextPc)
                                         (withNextPc (word.add m.(getNextPc) (word.of_Z 4)) m)))
    | EndCycleEarly _
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | GetCSRField _
    | SetCSRField _ _
    | GetPrivMode
    | SetPrivMode _
    | Fence _ _
        => fail_hard
    end.

  Definition device_step_without_IO(d: D): D :=
    fst (device.run1 d (false, false, word_to_bv (word.of_Z 0), word_to_bv (word.of_Z 0))).

  Fixpoint device_steps(n: nat): OState (ExtraRiscvMachine D) unit :=
    match n with
    | O => Return tt
    | S n' => updateExtra device_step_without_IO;; device_steps n'
    end.

  (* In the time that the riscv core needs to execute the i-th instruction, how many
     cycles does the device execute? *)
  Definition schedule := nat -> nat.

  Section WithSchedule.
    Context (sched: schedule).

    Definition nth_step(n: nat): OState (ExtraRiscvMachine D) unit :=
      device_steps (sched n);; free.interp_as_OState interpret_action (Run.run1 RV32IM).

    Fixpoint run_rec(steps_done steps_remaining: nat): OState (ExtraRiscvMachine D) unit :=
      match steps_remaining with
      | O => Return tt
      | S n => nth_step steps_done;; run_rec (S steps_done) n
      end.

    Definition run := run_rec 0.
  End WithSchedule.

End WithParams.
