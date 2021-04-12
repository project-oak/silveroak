Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import ListNotations.

Definition BASE_ADDR : Z := Ox"1000".

Instance consts : constants :=
  {| constants.STATUS_IDLE := 0;
     constants.STATUS_BUSY := 1;
     constants.STATUS_DONE := 2;
     constants.STATUS_ADDR := BASE_ADDR + Ox"0";
     constants.VALUE_ADDR := BASE_ADDR + Ox"4";
  |}.

Definition funcs := [put_wait_get].

Redirect "incrementwait.c" Compute c_module funcs.
