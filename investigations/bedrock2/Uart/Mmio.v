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

  (* sw/device/lib/base/mmio.h *)

  (****
     inline void mmio_region_write32(mmio_region_t base, ptrdiff_t offset,
                                     uint32_t value) {
       ((volatile uint32_t * )base.base)[offset / sizeof(uint32_t)] = value;
    }
   ***)

  Definition mmio_region_write32 : func :=
    let out := "out" in
    ("b2_mmio_region_write32", ([],[out],

    (cmd.set out (expr.literal 0))
    )).

  Definition mmio_region_read32 : func :=
    let out := "out" in
    ("b2_mmio_region_read32", ([],[out],
    (cmd.set out (expr.literal 0))
    )).


End Impl.
