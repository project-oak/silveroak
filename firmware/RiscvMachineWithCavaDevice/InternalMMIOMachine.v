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

Require Import Cava.TLUL.
Require Import Cava.Types.

Definition tl_h2d := denote_type TLUL.tl_h2d_t.

Definition tl_h2d_def :=
  (false, (0, (0, (0, (0, (0, (0, (0, (0, false)))))))))%N.

Ltac destruct_tl_h2d_step :=
  let t1 := eval unfold tl_h2d in tl_h2d in
  let t2 := eval simpl in t1 in
  match goal with
  | v : tl_h2d |- _ => unfold tl_h2d in v
  | v : t1 |- _ => simpl in v
  | v : t2 |- _ =>
    destruct v as (?a_valid, (?a_opcode, (?a_param, (?a_size, (?a_source,
                  (?a_address, (?a_mask, (?a_data, (?a_user, ?d_ready)))))))))
  end.

Ltac destruct_tl_h2d := repeat destruct_tl_h2d_step.

Definition a_valid   : tl_h2d -> bool. Proof. intros. destruct_tl_h2d. apply a_valid.   Defined.
Definition a_opcode  : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_opcode.  Defined.
Definition a_param   : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_param.   Defined.
Definition a_size    : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_size.    Defined.
Definition a_source  : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_source.  Defined.
Definition a_address : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_address. Defined.
Definition a_mask    : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_mask.    Defined.
Definition a_data    : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_data.    Defined.
Definition a_user    : tl_h2d -> N. Proof. intros. destruct_tl_h2d. apply a_user.    Defined.
Definition d_ready   : tl_h2d -> bool. Proof. intros. destruct_tl_h2d. apply d_ready.   Defined.

Definition update_tl_h2d
           (a_valid   : tl_h2d -> bool)
           (a_opcode  : tl_h2d -> N)
           (a_param   : tl_h2d -> N)
           (a_size    : tl_h2d -> N)
           (a_source  : tl_h2d -> N)
           (a_address : tl_h2d -> N)
           (a_mask    : tl_h2d -> N)
           (a_data    : tl_h2d -> N)
           (a_user    : tl_h2d -> N)
           (d_ready   : tl_h2d -> bool)
  : tl_h2d -> tl_h2d :=
  fun h2d => (a_valid h2d,
           (a_opcode h2d,
            (a_param h2d,
             (a_size h2d,
              (a_source h2d,
               (a_address h2d,
                (a_mask h2d,
                 (a_data h2d,
                  (a_user h2d, d_ready h2d))))))))).

Ltac tl_h2d_setter x :=
  let set_x :=
      (match eval pattern x in (update_tl_h2d a_valid a_opcode a_param a_size
                                              a_source a_address a_mask a_data
                                              a_user d_ready) with
       | ?set_x _ => constr:(fun v' => set_x (fun _ => v'))
       end) in
  exact set_x.

Definition set_a_valid   : bool -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_valid.   Defined.
Definition set_a_opcode  : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_opcode.  Defined.
Definition set_a_param   : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_param.   Defined.
Definition set_a_size    : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_size.    Defined.
Definition set_a_source  : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_source.  Defined.
Definition set_a_address : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_address. Defined.
Definition set_a_mask    : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_mask.    Defined.
Definition set_a_data    : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_data.    Defined.
Definition set_a_user    : N -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter a_user.    Defined.
Definition set_d_ready   : bool -> tl_h2d -> tl_h2d. Proof. tl_h2d_setter d_ready.   Defined.

Definition tl_d2h := denote_type TLUL.tl_d2h_t.

Definition tl_d2h_def :=
  (false, (0, (0, (0, (0, (0, (0, (0, (false, false)))))))))%N.

Ltac destruct_tl_d2h_step :=
  let t1 := eval unfold tl_d2h in tl_d2h in
  let t2 := eval simpl in t1 in
  match goal with
  | v : tl_d2h |- _ => unfold tl_d2h in v
  | v : t1 |- _ => simpl in v
  | v : t2 |- _ =>
    destruct v as (?d_valid, (?d_opcode, (?d_param, (?d_size, (?d_source,
                  (?d_sink, (?d_data, (?d_user, (?d_error, ?a_ready)))))))))
  end.

Ltac destruct_tl_d2h := repeat destruct_tl_d2h_step.

Definition d_valid  : tl_d2h -> bool. Proof. intros. destruct_tl_d2h. apply d_valid.  Defined.
Definition d_opcode : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_opcode. Defined.
Definition d_param  : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_param.  Defined.
Definition d_size   : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_size.   Defined.
Definition d_source : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_source. Defined.
Definition d_sink   : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_sink.   Defined.
Definition d_data   : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_data.   Defined.
Definition d_user   : tl_d2h -> N. Proof. intros. destruct_tl_d2h. apply d_user.   Defined.
Definition d_error  : tl_d2h -> bool. Proof. intros. destruct_tl_d2h. apply d_error.  Defined.
Definition a_ready  : tl_d2h -> bool. Proof. intros. destruct_tl_d2h. apply a_ready.  Defined.

Definition update_tl_d2h
           (d_valid  : tl_d2h -> bool)
           (d_opcode : tl_d2h -> N)
           (d_param  : tl_d2h -> N)
           (d_size   : tl_d2h -> N)
           (d_source : tl_d2h -> N)
           (d_sink   : tl_d2h -> N)
           (d_data   : tl_d2h -> N)
           (d_user   : tl_d2h -> N)
           (d_error  : tl_d2h -> bool)
           (a_ready  : tl_d2h -> bool)
  : tl_d2h -> tl_d2h :=
  fun d2h => (d_valid d2h,
           (d_opcode d2h,
            (d_param d2h,
             (d_size d2h,
              (d_source d2h,
               (d_sink d2h,
                (d_data d2h,
                 (d_user d2h,
                  (d_error d2h, a_ready d2h))))))))).

Ltac tl_d2h_setter x :=
  let set_x :=
      (match eval pattern x in (update_tl_d2h d_valid d_opcode d_param d_size
                                              d_source d_sink d_data d_user
                                              d_error a_ready) with
       | ?set_x _ => constr:(fun v' => set_x (fun _ => v'))
       end) in
  exact set_x.

Definition set_d_valid  : bool -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_valid.  Defined.
Definition set_d_opcode : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_opcode. Defined.
Definition set_d_param  : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_param.  Defined.
Definition set_d_size   : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_size.   Defined.
Definition set_d_source : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_source. Defined.
Definition set_d_sink   : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_sink.   Defined.
Definition set_d_data   : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_data.   Defined.
Definition set_d_user   : N -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_user.   Defined.
Definition set_d_error  : bool -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter d_error. Defined.
Definition set_a_ready  : bool -> tl_d2h -> tl_d2h. Proof. tl_d2h_setter a_ready. Defined.

Ltac tlsimpl :=
  cbn [tl_h2d_def
         a_valid a_opcode a_param a_size a_source a_address a_mask a_data a_user d_ready
         set_a_valid set_a_opcode set_a_param set_a_size set_a_source set_a_address
         set_a_mask set_a_data set_a_user set_d_ready
         tl_d2h_def
         d_valid d_opcode d_param d_size d_source d_sink d_data d_user d_error a_ready
         set_d_valid set_d_opcode set_d_param set_d_size set_d_source set_d_sink
         set_d_data set_d_user set_d_error set_a_ready] in *.

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
  Definition runUntilResp{D: device}(h2d: tl_h2d) :=
    fix rec(fuel: nat)(s: device.state): option tl_d2h * device.state :=
      let '(next, respo) := device.run1 s h2d in
      if fst respo then (Some respo, next) else
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

  Definition N_to_word(v: N): word :=
    word.of_Z (Z.of_N v).

  Definition word_to_N(w: word): N :=
    Z.to_N (word.unsigned w).

  Definition runUntilResp(h2d: tl_h2d):
    OState (ExtraRiscvMachine D) word :=
    mach <- get;
    let (respo, new_device_state) := device.runUntilResp h2d device.maxRespDelay
                                                         mach.(getExtraState) in
    put (withExtraState new_device_state mach);;
    resp <- fail_if_None respo;
    Return (N_to_word (d_data resp)).

  Definition mmioLoad(n: nat)(addr: word): OState (ExtraRiscvMachine D) (HList.tuple byte n) :=
    let h2d : tl_h2d :=
        set_a_valid true
        (set_a_opcode 4%N (* Get *)
        (set_a_size 2%N   (* 2^2 bytes *)
        (set_a_address (word_to_N addr)
        (set_d_ready true tl_h2d_def)))) in
    v <- runUntilResp h2d;
    Return (LittleEndian.split n (word.unsigned v)).

  Definition mmioStore(n: nat)(addr: word)(v: HList.tuple byte n): OState (ExtraRiscvMachine D) unit :=
    let h2d : tl_h2d :=
        set_a_valid true
        (set_a_opcode 0%N (* PutFullData *)
        (set_a_size 2%N   (* 2^2 bytes *)
        (set_a_address (word_to_N addr)
        (set_a_data (word_to_N (word.of_Z (LittleEndian.combine n v)))
        (set_d_ready true tl_h2d_def))))) in
    ignored <- runUntilResp h2d;
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
    fst (device.run1 d tl_h2d_def).

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
