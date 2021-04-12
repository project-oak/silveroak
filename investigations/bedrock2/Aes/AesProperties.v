Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.letexists.
Require Import Bedrock2Experiments.Aes.Aes.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Require Import bedrock2.FE310CSemantics.

Existing Instances common_h_impl aes_regs_h_impl.

Section Proofs.
  Context {fe310_parameters : FE310CSemantics.parameters.parameters}.

  (* Plugs in implicit arguments (otherwise [straightline] fails) *)
  Definition aes_init : Syntax.func := aes_init.

  Definition reg_write_event addr value
    : mem * string * list Semantics.word * (mem * list Semantics.word) :=
    (map.empty, REG32_SET, [addr;value], (map.empty, [])).

  Instance spec_of_aes_init : spec_of aes_init :=
    fun function_env =>
      forall tr mem (R : _ -> Prop) operation mode key_len
        ctrl_0 mode_mask mode_offset key_len_mask key_len_offset,
        R mem ->
        isMMIOAddr ctrl_0 ->
        word.unsigned ctrl_0 mod 4 = 0 ->
        let args := [operation; mode; key_len;
                    ctrl_0; operation; mode_mask; mode_offset;
                    key_len_mask; key_len_offset] in
        call function_env aes_init tr mem args
             (fun tr' mem' rets =>
                (* trace adds two write events *)
                (exists v, tr' = (reg_write_event ctrl_0 v)
                              :: (reg_write_event ctrl_0 v) :: tr)
                (* all the same properties hold on the memory state *)
                /\ R mem'
                (* no return values *)
                /\ rets = []).

  Lemma aes_init_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    (* process function-calling logic and up to first I/O *)
    repeat straightline.

    (* handle first register write *)
    eapply interact_nomem; [ solve [repeat straightline] | ].
    repeat letexists; split; [ exact eq_refl | ].
    ssplit; auto; [ ]. repeat straightline.

    (* handle second register write *)
    eapply interact_nomem; [ solve [repeat straightline] | ].
    repeat letexists; split; [ exact eq_refl | ].
    ssplit; auto; [ ]. repeat straightline.

    (* prove postcondition *)
    ssplit; auto; [ ].
    cbv [reg_write_event REG32_SET common_h_impl].
    eexists; reflexivity.
  Qed.
End Proofs.
