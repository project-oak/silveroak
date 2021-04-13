Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import ListNotations.
Local Open Scope Z_scope.

Definition BASE_ADDR : Z := Ox"1000".

Instance env : global_env :=
  {| global_env.STATUS_IDLE := 0;
     global_env.STATUS_BUSY := 1;
     global_env.STATUS_DONE := 2;
     global_env.STATUS_ADDR := BASE_ADDR + Ox"0";
     global_env.VALUE_ADDR := BASE_ADDR + Ox"4";
  |}.

Definition funcs {interp : constant.interp} := [put_wait_get].

(* Print with constants as variables *)
Existing Instance constant.var_interp.

(* Uncomment to print with constants as literals *)
(* Existing Instance constant.literal_interp. *)

Redirect "incrementwait.c" Compute c_module funcs.
