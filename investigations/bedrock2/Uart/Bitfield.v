Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.

Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).
  Local Notation "2" := (expr.literal 2) (in custom bedrock_expr).
  Local Notation "3" := (expr.literal 3) (in custom bedrock_expr).
  Local Notation "4" := (expr.literal 4) (in custom bedrock_expr).
  Local Notation "5" := (expr.literal 5) (in custom bedrock_expr).
  Local Notation "6" := (expr.literal 6) (in custom bedrock_expr).
  Local Notation "7" := (expr.literal 7) (in custom bedrock_expr).
  Local Notation "8" := (expr.literal 8) (in custom bedrock_expr).
  Local Notation "9" := (expr.literal 9) (in custom bedrock_expr).

  (* sw/device/lib/base/bitfield.h *)
  Definition bitfield_field32_write : func :=
    let ret := "ret" in
    ("b2_bitfield_field32_write", ([],[ret],
    (cmd.set ret (expr.literal 0))
    )).

  Definition bitfield_bit32_write : func :=
    let ret := "ret" in
    ("b2_bitfield_bit32_write", ([],[ret],
    (cmd.set ret (expr.literal 0))
    )).

  Definition bitfield_bit32_read : func :=
    let ret := "ret" in
    ("b2_bitfield_bit32_read", ([],[ret],
    (cmd.set ret (expr.literal 0))
    )).

End Impl.

