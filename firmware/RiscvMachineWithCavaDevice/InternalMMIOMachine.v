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
Require Export Cava.TLUL.

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
    run1: (* input: TileLink host-2-device *)
      state -> tl_h2d ->
      (* output: next state, TileLink device-2-host *)
      state * tl_d2h;

    (* lowest address of the MMIO address range used to communicate with this device *)
    addr_range_start: Z;

    (* one past the highest MMIO address *)
    addr_range_pastend: Z;

    (* max number of device cycles this device takes to serve read/write requests, ie
       max number of run1 calls with active read/write request until the device responds *)
    maxRespDelay: state -> tl_h2d -> nat;
  }.
  (* Note: there are two levels of "polling until a response is available":
     - on the hardware level, using runUntilResp, which appears as
       blocking I/O for the software
     - on the software level, using MMIO reads on some status register,
       where the MMIO read immediately gives a "busy" response, and the
       software keeps polling until the MMIO read returns a "done" response *)

  (* returning None means out of fuel and must not happen if fuel >= device.maxRespDelay.
     It is also assumed that [a_valid h2d = true] and [d_ready h2d = true]. *)
  Definition runUntilResp{D: device}(h2d: tl_h2d)(fuel: nat)(s: device.state) :=
    let fix receive(fuel: nat)(s: device.state): option tl_d2h * device.state :=
        let '(next, d2h) := device.run1 s (set_d_ready true tl_h2d_default) in
        if d_valid d2h then (Some d2h, next) else
          match fuel with
          | O => (None, next)
          | S fuel' => receive fuel' next
          end in

    let fix send(fuel: nat)(s: device.state)(prev_a_ready: bool): option tl_d2h * device.state :=
        let '(next, d2h) := device.run1 s h2d in
        if prev_a_ready then
          if d_valid d2h then (Some d2h, next) else
          match fuel with
          | O => (None, next)
          | S fuel' => receive fuel' next
          end
        else
          match fuel with
          | O => (None, next)
          | S fuel' => send fuel' next (a_ready d2h)
          end in

    (* As we don't know yet if the device is listening (on channel A), we have
       to send an empty h2d packet first. Perhaps we should keep track of the
       last a_ready value so we don't have to do this? *)
    let '(next, d2h) := device.run1 s tl_h2d_default in
    send fuel next (a_ready d2h).

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

  Definition N_to_word(v: N): word :=
    word.of_Z (Z.of_N v).

  Definition word_to_N(w: word): N :=
    Z.to_N (word.unsigned w).

  Definition runUntilResp(h2d: tl_h2d):
    OState (ExtraRiscvMachine D) word :=
    mach <- get;
    let (respo, new_device_state) :=
        device.runUntilResp h2d (device.maxRespDelay mach.(getExtraState) h2d)
                            mach.(getExtraState) in
    put (withExtraState new_device_state mach);;
    resp <- fail_if_None respo;
    Return (N_to_word (d_data resp)).

  Definition mmioLoad(log2_nbytes: nat)(addr: word)
    : OState (ExtraRiscvMachine D) (HList.tuple byte (2 ^ log2_nbytes)) :=
    let h2d : tl_h2d :=
        set_a_valid true
        (set_a_opcode Get
        (set_a_size (N.of_nat log2_nbytes)
        (set_a_address (word_to_N addr)
        (set_d_ready true tl_h2d_default)))) in
    v <- runUntilResp h2d;
    Return (LittleEndian.split (2 ^ log2_nbytes) (word.unsigned v)).

  Definition mmioStore(log2_nbytes: nat)(addr: word)(v: HList.tuple byte (2 ^ log2_nbytes))
    : OState (ExtraRiscvMachine D) unit :=
    let h2d : tl_h2d :=
        set_a_valid true
        (set_a_opcode PutFullData
        (set_a_size (N.of_nat log2_nbytes)
        (set_a_address (word_to_N addr)
        (set_a_data (Z.to_N (LittleEndian.combine (2 ^ log2_nbytes) v))
        (set_d_ready true tl_h2d_default))))) in
    ignored <- runUntilResp h2d;
    Return tt.

  Definition loadN(log2_nbytes: nat)(kind: SourceType)(a: word):
    OState (ExtraRiscvMachine D) (HList.tuple byte (2 ^ log2_nbytes)) :=
    mach <- get;
    match Memory.load_bytes (2 ^ log2_nbytes) mach.(getMachine).(getMem) a with
    | Some v =>
      match kind with
      | Fetch => if isXAddr4B a mach.(getMachine).(getXAddrs) then Return v else fail_hard
      | _ => Return v
      end
    | None => if device.isMMIOAddrB a (2 ^ log2_nbytes) then mmioLoad log2_nbytes a else fail_hard
    end.

  Definition storeN(log2_nbytes: nat)(kind: SourceType)(a: word)(v: HList.tuple byte ( 2 ^ log2_nbytes)) :=
    mach <- get;
    match Memory.store_bytes (2 ^ log2_nbytes) mach.(getMachine).(getMem) a v with
    | Some m => update (withMem m)
    | None => if device.isMMIOAddrB a (2 ^ log2_nbytes) then mmioStore log2_nbytes a v else fail_hard
    end;;
    update (fun mach => withXAddrs (invalidateWrittenXAddrs (2 ^ log2_nbytes) a mach.(getXAddrs)) mach).

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
    | LoadByte ctxid a => loadN 0 ctxid a
    | LoadHalf ctxid a => loadN 1 ctxid a
    | LoadWord ctxid a => loadN 2 ctxid a
    | LoadDouble ctxid a => loadN 3 ctxid a
    | StoreByte ctxid a v => storeN 0 ctxid a v
    | StoreHalf ctxid a v => storeN 1 ctxid a v
    | StoreWord ctxid a v => storeN 2 ctxid a v
    | StoreDouble ctxid a v => storeN 3 ctxid a v
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
    let '(next_state, ignored_d2h) := (device.run1 d tl_h2d_default) in next_state.

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

    Definition run(steps_remaining: nat)(s: ExtraRiscvMachine D): option (ExtraRiscvMachine D) :=
      match run_rec 0 steps_remaining s with
      | (Some tt, final) => Some final
      | (None, _) => None
      end.
  End WithSchedule.

End WithParams.
