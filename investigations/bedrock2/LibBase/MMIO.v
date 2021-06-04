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
    let base := "base" in
    let offset := "offset" in
    let value := "value" in
    ("b2_mmio_region_write32", ([base; offset; value],[],
    bedrock_func_body:(
      store4(base + offset, value)
    ))).

  (****
    inline uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset) {
      return ((volatile uint32_t * )base.base)[offset / sizeof(uint32_t)];
    }
  ***)
  Definition mmio_region_read32 : func :=
    let base := "base" in
    let offset := "offset" in
    let out := "out" in
    ("br2_mmio_region_read32", ([base; offset],[out],
    bedrock_func_body:(
      out = load4(base + offset)
    ))).


End Impl.
