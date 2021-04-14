Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instance constants.constant_names.

Definition funcs := [put_wait_get].
Redirect "incrementwait.c" Compute c_module funcs.
