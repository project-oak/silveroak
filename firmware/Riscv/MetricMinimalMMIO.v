(* Copied from riscv.Platform.MetricMinimalMMIO, but using
   Bedrock2Experiments.Riscv.MinimalMMIO instead of riscv.Platform.MinimalMMIO,
   and using the same MaterializeRiscvProgram.Materialize instance instead of
   a metrics-specific instance (while still computing metrics) *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import Bedrock2Experiments.Riscv.MinimalMMIO.
Require Import riscv.Platform.MetricLogging.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Import MetricRiscvMachine.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Import List.
  Import free.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  (* note: ext_spec does not have access to the metrics *)
  Context {mmio_spec: MMIOSpec}.

  Local Notation M := (free riscv_primitive primitive_result).

  Definition metrics_of(p: riscv_primitive): MetricLog -> MetricLog :=
    match p with
    | GetRegister a => id
    | SetRegister a b => id
    | LoadByte a b => addMetricLoads 1
    | LoadHalf a b => addMetricLoads 1
    | LoadWord a b => addMetricLoads 1
    | LoadDouble a b => addMetricLoads 1
    | StoreByte a b c => addMetricStores 1
    | StoreHalf a b c => addMetricStores 1
    | StoreWord a b c => addMetricStores 1
    | StoreDouble a b c => addMetricStores 1
    | MakeReservation a => id
    | ClearReservation a => id
    | CheckReservation a => id
    | GetCSRField f => id
    | SetCSRField f v => id
    | GetPrivMode => id
    | SetPrivMode m => id
    | Fence a b => id
    | GetPC => id
    | SetPC a => addMetricJumps 1
    | EndCycleNormal => addMetricInstructions 1
    | EndCycleEarly A => addMetricInstructions 1
    end.

  Definition interp_action p metmach post :=
    interpret_action p (metmach.(getMachine))
      (fun r mach => post r (mkMetricRiscvMachine mach (metrics_of p (metmach.(getMetrics)))))
      (fun _ => False).

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.
  Arguments LittleEndian.combine: simpl never.

  Global Instance MetricMinimalMMIOPrimitivesParams: PrimitivesParams M MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := Primitives.nonmem_load (PrimitivesParams := MinimalMMIOPrimitivesParams);
    Primitives.nonmem_store := Primitives.nonmem_store (PrimitivesParams := MinimalMMIOPrimitivesParams);
    Primitives.valid_machine mach :=
      map.undef_on mach.(getMem) isMMIOAddr /\
      PropSet.disjoint (PropSet.of_list mach.(getXAddrs)) isMMIOAddr;
  }.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MetricMinimalMMIOPrimitivesParams Monad_free Bind Return].
    { symmetry. eapply interp_bind_ex_mid; intros.
      eapply MinimalMMIO.interpret_action_weaken_post; eauto; cbn; eauto. }
    { symmetry. rewrite interp_ret; eapply iff_refl. }
  Qed.

  Lemma interp_action_weaken_post a (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s) s
    : interp_action a s post1 -> interp_action a s post2.
  Proof. eapply MinimalMMIO.interpret_action_weaken_post; eauto. Qed.
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ endswith s'.(getLog) s.(getLog)).
  Proof. eapply MinimalMMIO.interpret_action_appendonly''; eauto. Qed.
  Lemma interp_action_total{memOk: map.ok Mem} a s post :
    map.undef_on s.(getMachine).(getMem) isMMIOAddr ->
    PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr ->
    interp_action a s post ->
    exists v s, post v s /\ map.undef_on s.(getMem) isMMIOAddr /\
                PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr.
  Proof.
    intros H D H1.
    unshelve epose proof (MinimalMMIO.interpret_action_total _ _ _ _ _ D H1) as H0; eauto.
    destruct H0 as (?&?&?&[[]|(?&?)]); eauto.
  Qed.
  Lemma interp_action_preserves_valid{memOk: map.ok Mem} a s post :
    map.undef_on s.(getMachine).(getMem) isMMIOAddr ->
    PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr ->
    interp_action a s post ->
    interp_action a s (fun v s' =>
        post v s' /\
        map.undef_on s'.(getMem) isMMIOAddr /\
        PropSet.disjoint (PropSet.of_list s'.(getMachine).(getXAddrs)) isMMIOAddr).
  Proof.
    intros U D I.
    unshelve epose proof (MinimalMMIO.interpret_action_preserves_valid' _ _ _ U D I) as H0; eauto.
  Qed.

  Global Instance MetricMinimalMMIOPrimitivesSane{memOk: map.ok Mem} :
    MetricPrimitivesSane MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane valid_machine MetricMinimalMMIOPrimitivesParams];
      intros *; intros [U D] M;
      (split; [ exact (interp_action_total _ st _ U D M)
              | eapply interp_action_preserves_valid; try eassumption;
                eapply interp_action_appendonly'; try eassumption ]).
  Qed.

  Global Instance MetricMinimalMMIOSatisfiesPrimitives{memOk: map.ok Mem}:
    MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MetricMinimalMMIOPrimitivesParams invalidateWrittenXAddrs].
    all: intros; destruct initialL;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple] in *
      | _ => progress cbv [id valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || blia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct getMachine; eassumption.
  Qed.

End Riscv.
