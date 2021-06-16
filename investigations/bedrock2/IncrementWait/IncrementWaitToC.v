Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instance constant_names.

Require Import bedrock2.Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  (* Note: run using make/coqc to avoid IDE bugs causing missing newlines or spurious <infomsg>*)
  Redirect "incrementwait.c"
    let c_code := eval compute in (byte_list_of_string (c_module [put_wait_get])) in idtac c_code.
Abort.
