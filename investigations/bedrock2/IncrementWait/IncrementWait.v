Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).

  (* Sets the VALUE register, waits for a DONE status, reads the result, and
     returns it. Assumes the circuit is in IDLE state at the start. *)
  Definition put_wait_get : func :=
    (* input variables *)
    let input := "input" in
    (* output variables *)
    let out := "out" in
    (* temporary variables *)
    let status := "status" in
    ("put_wait_get",
     ([input], [out], bedrock_func_body:(
        (* write input value *)
        output! WRITE (VALUE_ADDR, input) ;
        (* initialize status to 0 *)
        status = 0 ;
        (* wait for status to be DONE *)
        while ((status & (1 << STATUS_DONE)) == 0) {
          io! status = READ ( STATUS_ADDR )
        };
        (* read the value and exit *)
        io! out = READ ( VALUE_ADDR )
    ))).
End Impl.
