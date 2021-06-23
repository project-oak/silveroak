Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.Simp.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.ExtSpecExtends.

Section WithParameters.
  Import StateMachineSemantics.parameters.
  Context {width word mem}
          (p1: parameters width word mem)
          (p2: parameters width word mem).

  Class state_machine_extends_params := {
    (* abstract an extended state into a simplified state, discarding additional data *)
    abs_state: state (parameters := p1) -> state (parameters := p2);

    (* extend a simplified state into an extended state by adding default values *)
    ext_state: state (parameters := p2) -> state (parameters := p1);

    (* translate a register name of the simplified state machine into one of the extended machine *)
    ext_register: register (parameters := p2) -> register (parameters := p1);
  }.

  Context {ep: state_machine_extends_params}.

  Record state_machine_extends := {
    abs_ext_state: forall s2, abs_state (ext_state s2) = s2;
    ext_register_inj: forall r2 r2', ext_register r2 = ext_register r2' -> r2 = r2';
    is_initial_state_12: forall s1, is_initial_state s1 -> is_initial_state (abs_state s1);
    is_initial_state_21: forall s2, is_initial_state s2 -> is_initial_state (ext_state s2);
    reg_addr_compat: forall r2, reg_addr (ext_register r2) = reg_addr r2;
    is_reg_addr_21: forall a, is_reg_addr (parameters := p2) a -> is_reg_addr (parameters := p1) a;

    (* for each read step in the extended machine, it must also exist in the simplified machine,
       or, if we want to delete that step, we must delete all steps starting from that state s1
       and having register r2 as input, to make sure we don't miss some nondeterministic options *)
    read_step_12: forall s1 r2 v s1', read_step (parameters := p1) s1 (ext_register r2) v s1' ->
                                      read_step (parameters := p2) (abs_state s1) r2 v (abs_state s1')
                                   \/ (~exists v0 s0,
                                      read_step (parameters := p2) (abs_state s1) r2 v0 s0);

    (* the other direction is simpler: each read_step of the simplified machine must also be in the
       extended machine: *)
    read_step_21: forall s2 r2 v s2', read_step (parameters := p2) s2 r2 v s2' ->
      read_step (parameters := p1) (ext_state s2) (ext_register r2) v (ext_state s2');

    (* similar conditions for write steps, but there, the value is considered an input instead of
       output *)
    write_step_12: forall s1 r2 v s1', write_step (parameters := p1) s1 (ext_register r2) v s1' ->
                                 write_step (parameters := p2) (abs_state s1) r2 v (abs_state s1')
                             \/ (~exists s0,
                                 write_step (parameters := p2) (abs_state s1) r2 v s0);

    write_step_21: forall s2 r2 v s2', write_step (parameters := p2) s2 r2 v s2' ->
      write_step (parameters := p1) (ext_state s2) (ext_register r2) v (ext_state s2');
  }.

  Context {p1_ok: parameters.ok p1} {p2_ok: parameters.ok p2}.

  Definition espec1 := ext_spec (p := p1).
  Definition espec2 := ext_spec (p := p2).

  Hypothesis se: state_machine_extends.

  Lemma step_21: forall action s2 args rets s2',
      step (p := p2) action s2 args rets s2' ->
      step (p := p1) action (ext_state s2) args rets (ext_state s2').
  Proof.
    unfold step. intros.
    destruct_one_match.
    + (* WRITE *)
      simp. eexists. ssplit.
      * eapply se.(reg_addr_compat).
      * reflexivity.
      * eapply se.(write_step_21). assumption.
    + destruct_one_match. 2: contradiction.
      (* READ *)
      simp. eexists _, _. ssplit.
      * eapply se.(reg_addr_compat).
      * reflexivity.
      * eapply se.(read_step_21). assumption.
  Qed.

  Lemma execution_21: forall t s2, execution t s2 -> execution t (ext_state s2).
  Proof.
    induction t; simpl; intros.
    - eapply se.(is_initial_state_21). assumption.
    - simp. eauto using step_21.
  Qed.

  Lemma espec1_extends_espec2: ext_spec_extends espec1 espec2.
  Proof.
    unfold ext_spec_extends, espec1, espec2, ext_spec.
    intros.
    destruct_one_match.
    + (* WRITE *)
      admit.
    + destruct_one_match. 2: contradiction.
      (* READ *)
      subst action. clear E.
      simp. eexists _, _. ssplit.
      * reflexivity.
      * reflexivity.
      * eapply se.(reg_addr_compat).
      * eauto 10 using execution_21, read_step_21.
      * intros.
        eapply Hp1.
        (* tricky part: going from 1 (extended) to 2 (simplified) machine *)
        -- admit.
        -- eapply se.(read_step_12) in H0. destruct H0 as [R | R]. 1: exact R.
           exfalso. apply R. eexists _, _.

  Abort.
End WithParameters.
