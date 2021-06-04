(* based on riscv.Platform.MinimalMMIO *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Export riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.ListSet.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MaterializeRiscvProgram.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Platform.Sane.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import riscv.Platform.Run.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Class MMIOSpec{W: Words}{Mem : map.map word byte}(E: Type) := {
  (* should not say anything about alignment, just whether it's in the MMIO range *)
  (* tells whether the addr is used to communicate with an external device *)
  isExternalMMIOAddr: word -> Prop;
  (* isInternalMMIOAddr is already checked as part of internalMMIORead/Write *)

  (* alignment and load size checks *)
  isMMIOAligned: nat -> word -> Prop;

  internalMMIORead: word -> E -> (word -> E -> Prop) -> Prop;
  internalMMIOWrite: word -> word -> E -> (E -> Prop) -> Prop;

  (* at any point, the extra state (internal device) can concurrently make a step *)
  extra_step: E -> (E -> Prop) -> Prop;

  (* hardware guarantees on MMIO read values *)
  externalMMIOReadOK : nat -> list LogItem -> word -> word -> Prop;
}.

Section Riscv.
  Import free.
  Context {W: Words} {Mem: map.map word byte} {Registers: map.map Register word}.

  Definition mmioLoadEvent(addr: word)(v: word): LogItem :=
    ((map.empty, "MMIOREAD"%string, [addr]), (map.empty, [v])).

  Definition mmioStoreEvent(addr: word)(v: word): LogItem :=
    ((map.empty, "MMIOWRITE"%string, [addr; v]), (map.empty, [])).

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Context {E: Type} {mmio_spec: MMIOSpec E}.

  Definition nonmem_store(n: nat)(ctxid: SourceType)(a v: word)
             (mach: ExtraRiscvMachine E) post :=
    isMMIOAligned n a /\
    let mach' := withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) mach in
    ((internalMMIOWrite a v mach.(getExtraState)
                        (fun e' => post (withExtraState e' mach'))) \/
     (isExternalMMIOAddr a /\
      post (withLogItem (mmioStoreEvent a v) mach'))).

  Definition store(n: nat)(ctxid: SourceType) a v (mach: ExtraRiscvMachine E) post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs))
                                 (withMem m mach))
    | None => nonmem_store n ctxid a (signedByteTupleToReg v) mach post
    end.

  Definition nonmem_load(n: nat)(ctxid: SourceType) a (mach: ExtraRiscvMachine E)
             (post: _ -> _ -> Prop) :=
    isMMIOAligned n a /\
    ((internalMMIORead a mach.(getExtraState)
                       (fun v e' => post v (withExtraState e' mach))) \/
     (isExternalMMIOAddr a /\
      (* there exists at least one valid MMIO read value (set is nonempty) *)
      (exists v, externalMMIOReadOK n (getLog mach) a v) /\
      (* ...and postcondition holds for all valid read values *)
      forall v,
        externalMMIOReadOK n (getLog mach) a v ->
        post v (withLogItem (mmioLoadEvent a v) mach))).

  Definition load(n: nat)(ctxid: SourceType) a (mach: ExtraRiscvMachine E) post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach
                 (fun v mach => post (LittleEndian.split n (word.unsigned v)) mach)
    end.

  Definition updatePc(mach: ExtraRiscvMachine E): ExtraRiscvMachine E :=
    (withPc mach.(getNextPc)
    (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach)).

  Definition interpret_action (a : riscv_primitive) (mach : ExtraRiscvMachine E) :
    (primitive_result a -> ExtraRiscvMachine E -> Prop) ->
    (ExtraRiscvMachine E -> Prop) -> Prop :=
    match a with
    | GetRegister reg => fun (postF: word -> ExtraRiscvMachine E -> Prop) postA =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach.(getRegs) reg with
               | Some x => x
               | None => word.of_Z 0 end in
        postF v mach
    | SetRegister reg v => fun postF postA =>
      let regs := if Z.eq_dec reg Register0
                  then mach.(getRegs)
                  else map.put mach.(getRegs) reg v in
      postF tt (withRegs regs mach)
    | GetPC => fun postF postA => postF mach.(getPc) mach
    | SetPC newPC => fun postF postA => postF tt (withNextPc newPC mach)
    | LoadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | LoadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | LoadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | LoadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | StoreByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | StoreHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | StoreWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | StoreDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | EndCycleNormal => fun postF postA => postF tt (updatePc mach)
    | EndCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | GetCSRField _
    | SetCSRField _ _
    | GetPrivMode
    | SetPrivMode _
    | Fence _ _
        => fun postF postA => False
    end.

  Let M: Type -> Type := free riscv_primitive primitive_result.

  Definition mcomp_sat{A: Type}(m: M A)(initial: ExtraRiscvMachine E)
             (post: A -> ExtraRiscvMachine E -> Prop): Prop :=
    @free.interpret _ _ _ interpret_action A m initial post (fun _ => False).

  Definition processor_step(initial: ExtraRiscvMachine E)
             (post: ExtraRiscvMachine E -> Prop): Prop :=
    mcomp_sat (run1 RV32IM) initial (fun dummy_unit final => post final).

  Definition device_step(initial: ExtraRiscvMachine E)
             (post: ExtraRiscvMachine E -> Prop): Prop :=
    extra_step initial.(getExtraState) (fun e => post (withExtraState e initial)).

  (* `system_step` chooses nondeterministically whether a step happens in the
     processor or in the device, therefore the set `post` must be big
     enough to allow for both, and the next step (as invoked by runsTo)
     will continue with any state from `post` *)
  Definition system_step(initial: ExtraRiscvMachine E)
             (post: ExtraRiscvMachine E -> Prop): Prop :=
    processor_step initial post /\ device_step initial post.

End Riscv.
