Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Bedrock2Experiments.Aes.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Require Import bedrock2.FE310CSemantics.

SearchHead Semantics.parameters.
Existing Instances common_h_impl aes_regs_h_impl aes_h_impl.

Section Proofs.
  Context {fe310_parameters : FE310CSemantics.parameters.parameters}.

  (* For now, empty spec *)
  Instance spec_of_aes_init : spec_of aes_init :=
    fun functions =>
      forall tr mem aes_cfg_operation aes_cfg_mode aes_cfg_key_len aes_ctrl_shadowed_0
        operation mode_mask mode_offset key_len_mask key_len_offset,
        isMMIOAddr aes_ctrl_shadowed_0 ->
        word.unsigned aes_ctrl_shadowed_0 mod 4 = 0 ->
        let args := [aes_cfg_operation; aes_cfg_mode; aes_cfg_key_len;
                    aes_ctrl_shadowed_0; operation; mode_mask; mode_offset;
                    key_len_mask; key_len_offset] in
        call functions aes_init tr mem args
             (fun tr m rets => True).

  Lemma aes_init_no_struct_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    Fail straightline. (* FIXME *)
    (* This should be a call to [enter], but I got errors from it saying
       aes_init was not evaluable when it was a bound variable. Unclear why, but
       I inlined the tactic here and removed the binding *)
    cbv beta delta [program_logic_goal_for]; intros; bind_body_of_function aes_init;
    (let fdefn := eval cbv delta [aes_init] in aes_init in
     let ctx := string2ident.learn fdefn in
     let H := fresh "_string_to_ident" in
     pose (H := ctx); lazymatch goal with
                      | |- ?s _ => cbv beta delta [s]
                      end).

    (* simplification *)
    cbv zeta.

    (* (modified) rest of the first straightline clause *)
    (intros; unfold1_call_goal; cbv beta match delta [call_body];
     lazymatch goal with
     | |- if ?test then ?T else _ => replace test with true by reflexivity; change T
     end; cbv beta match delta [func]).

    (* finally, enter the body of the function *)
    repeat straightline.
    eapply interact_nomem; [ solve [repeat straightline] | ].
    cbn [Semantics.ext_spec ext_spec semantics_parameters].
    cbv [ext_spec]. rewrite String.eqb_refl.
    do 2 eexists; ssplit; auto; [ ].

    repeat straightline.
    eapply interact_nomem; [ solve [repeat straightline] | ].
    cbn [Semantics.ext_spec ext_spec semantics_parameters].
    cbv [ext_spec]. rewrite String.eqb_refl.
    do 2 eexists; ssplit; auto; [ ].

    repeat straightline.
  Qed.
End Proofs.
