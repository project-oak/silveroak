Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.
  Context {consts : constants}.
  Import constants.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).

  (* Sets the VALUE register, waits for a DONE status until a particular timeout
     (in terms of number of attempted reads), reads the result, and returns
     it. Fails if the circuit is not in IDLE state at the start, or if the
     status is not DONE by the time the timeout is reached. *)
  Definition put_wait_get : func :=
    (* input variables *)
    let input := "input" in
    let timeout := "timeout" in
    (* output variables *)
    let out := "out" in
    let success := "success" in
    (* temporary variables *)
    let status := "status" in
    ("put_wait_get",
     ([input; timeout], [out; success], bedrock_func_body:(
        io! status = READ ( STATUS_ADDR ) ;
        (* default output values *)
        success = 0 ;
        out = 0 ;
        (* only proceed if status is idle *)
        if (status & (1 << STATUS_IDLE)) {
          (* write input value *)
          output! WRITE (VALUE_ADDR, input) ;
          (* wait for a DONE status or a timeout *)
          while (timeout) {
            io! status = READ ( STATUS_ADDR ) ;
            if (status & (1 << STATUS_DONE)) {
              (* if the status is DONE, read the value and exit successfully *)
              io! out = READ ( VALUE_ADDR ) ;
              success = 1 ;
              timeout = 0
            } else {
              (* otherwise, continue the loop *)
              timeout = timeout - 1
            }
          }
        }
    ))).
End Impl.
