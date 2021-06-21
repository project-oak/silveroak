Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.TailRecursion.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Z.Lia.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.Uart.UartSemantics.
Require Import Bedrock2Experiments.Uart.Uart.
Require Import Bedrock2Experiments.Uart.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* bedrock2.ProgramLogic does cbv, which unfolds the getters of aes_constants,
   resulting in large ugly ASTs *)
Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.

Section Proofs.
  Context {p : UartSemantics.parameters} {p_ok : parameters.ok p}
          {consts : uart_constants Z}.
  Context {consts_ok : uart_constants_ok consts}.
  Existing Instance state_machine_parameters.

  (* this duplicate of locals_ok helps when Semantics.word has been changed to
     parameters.word *)
  Local Instance localsok : @map.ok string parameters.word Semantics.locals
     := Semantics.locals_ok.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (p:=state_machine_parameters)).

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := parameters.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := parameters.word)),
         constants [Properties.word_cst]).

  Existing Instance constant_literals | 10.

  (***** Proofs for specific functions *****)

  Global Instance spec_of_uart_tx_idle : spec_of "b2_uart_tx_idle" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
      (* no special requirements of the memory *)
      R m ->
      (* no constraints on current state *)
      execution tr s ->
      call function_env uart_tx_idle tr m []
        (fun tr' m' rets =>
          exists (status out : Semantics.word) (s' : state),
            (* the new state matches the new trace *)
            execution tr' s'
            (* ...and there exists a single valid status-read step between
               the old and new state, and the read result was [status] *)
            /\ read_step s STATUS status s'
            (* ...and all the same properties as before hold on the memory *)
            /\ R m'
            (* ...and there is one output value *)
            /\ rets = [status]
            (* ...and the output value is one if and only if the
               txidle flag is set *)
            /\ word.eqb out (word.of_Z 1)
              = is_flag_set status UART_STATUS_TXIDLE_BIT).
  (*
  Lemma uart_tx_idle_correct :
    program_logic_goal_for_function! uart_tx_idle.
  Proof.
     Admitted.*)
End Proofs.
