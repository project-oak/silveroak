Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require Import Bedrock2Experiments.Aes.Aes.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instance constants.constant_names.

Definition funcs := [aes_init].
Redirect "aes.c" Compute c_module funcs.
