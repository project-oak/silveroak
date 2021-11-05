Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Tactics.fwd.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.Pipeline.
Require Import Bedrock2Experiments.List.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitProperties.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Import Syntax.Coercions.
Local Open Scope string_scope.

Lemma put_wait_get_correct' fs input (R: mem -> Prop) (t : trace) m :
  R m ->
  execution t IDLE ->
  WeakestPrecondition.call (put_wait_get :: fs) IncrementWait.put_wait_get t m [input]
         (fun t' m' retvals => execution t' IDLE /\ R m' /\ retvals = [proc input]).
Proof.
  pose proof (put_wait_get_correct fs) as P.
  unfold spec_of_put_wait_get in P.
  apply P.
Qed.

(* Location in the instructions that marks the start of the [main] routine *)
Definition put_wait_get_relative_pos : Z.
  let x := constr:(map.get
                     (snd (fst put_wait_get_compile_result))
                     put_wait_get) in
  let x := eval vm_compute in x in
      lazymatch x with
      | Some (_, _, ?y) => exact y
      end.
Defined.

Definition stack_start: word := word.of_Z (8*2^10).
Definition stack_pastend: word := word.of_Z (16*2^10).

Lemma funcs_valid: ExprImp.valid_funs (map.of_list funcs).
Proof.
  cbv [funcs map.of_list ExprImp.valid_funs put_wait_get]. intros *.
  rewrite !map.get_put_dec, map.get_empty.
  repeat destruct_one_match; inversion 1; cbv [ExprImp.valid_fun].
  all:ssplit.
  all:apply dedup_NoDup_iff.
  all:reflexivity.
Qed.

Lemma put_wait_get_asm_correct
      input (R Rdata Rexec: mem -> Prop)
      (p_functions ret_addr : word)
      (mem : mem)
      (initial : MetricRiscvMachine) :
  (* given that some property holds about the initial memory... *)
  R mem ->
  (* ...and the trace so far leads to an IDLE state... *)
  execution (getLog initial) IDLE ->
  (* ...and the current machine state is OK... *)
  let instrs := fst (fst (put_wait_get_compile_result)) in
  LowerPipeline.machine_ok
    p_functions
    stack_start stack_pastend
    instrs mem Rdata Rexec initial ->
  (* ...and the pc points to the beginning of get_put_wait... *)
  initial.(getPc) = word.add p_functions (word.of_Z put_wait_get_relative_pos) ->
  (* ...the first argument register contains the input value... *)
  map.get initial.(getRegs) RegisterNames.a0 = Some input ->
  (* ...and the ra register contains some aligned return address... *)
  word.unsigned ret_addr mod 4 = 0 ->
  map.get initial.(getRegs) RegisterNames.ra = Some ret_addr ->
  (* ...then, after the [put_wait_get] routine is executed... *)
  runsTo initial
         (fun final : MetricRiscvMachine =>
            exists mem',
              (* ...the first return value register contains the expected result... *)
              map.get final.(getRegs) RegisterNames.a0 = Some (proc input)
              (* ...execution will continue at the return address that was in the ra register...*)
              /\ final.(getPc) = ret_addr
              (* ...the counter device ends up in an IDLE state... *)
              /\ execution final.(getLog) IDLE
              (* ...the memory is unchanged (as in, still satisfies R)... *)
              /\ R mem'
              (* ...and the new machine state is OK *)
              /\ LowerPipeline.machine_ok
                  p_functions
                  stack_start stack_pastend
                  instrs mem' Rdata Rexec final).
Proof.
  intros.
  pose proof compiler_correct_wp as P.
  specialize P with (fs := funcs) (stack_hi := stack_pastend) (stack_lo := stack_start).
  specialize P with (fname := put_wait_get) (p_funcs := p_functions).
  match type of P with
  | context[?fs] => lazymatch fs with
                    | (map.of_list funcs) =>
                      let fs' := eval cbv [map.of_list put_wait_get funcs] in fs in
                          change fs with fs' in P
                   end
  end.
  eapply runsToNonDet.runsTo_weaken.
  1: eapply P.
  { eapply compile_ext_call_correct. }
  { intros. reflexivity. }
  { exact funcs_valid. }
  { apply dedup_NoDup_iff. reflexivity. }
  { apply put_wait_get_compile_result_eq. }
  { eapply put_wait_get_correct' with (R := R); eassumption. }
  { reflexivity. }
  { vm_compute. congruence. }
  { reflexivity. }
  { assumption. }
  { eassumption. }
  { assumption. }
  { cbn -[map.get].
    match goal with
    | H: map.get _ RegisterNames.a0 = Some input |-
      match ?x with _ => _ end = _ => replace x with (Some input)
    end.
    reflexivity. }
  { reflexivity. }
  { eassumption. }
  { cbv beta. clear. intros.
    cbn -[map.get proc] in *. fwd. eauto 10. }
Qed.
