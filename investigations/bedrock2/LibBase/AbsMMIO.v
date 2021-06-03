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
     inline void abs_mmio_write32(uint32_t addr, uint32_t value) {
       *((volatile uint32_t * )addr) = value;
     }
   ***)
  Definition abs_mmio_write32 : func :=
    let addr := "addr" in
    let value := "value" in
    ("b2_abs_mmio_write32", ([addr; value],[],
    bedrock_func_body:(
      store4(addr, value)
    ))).

  (****
     inline uint32_t abs_mmio_read32(uint32_t addr) {
       return *((volatile uint32_t * )addr);
     }
  ***)
  Definition abs_mmio_read32 : func :=
    let addr := "addr" in
    let out := "out" in
    ("br2_abs_mmio_read32", ([addr],[out],
    bedrock_func_body:(
      out = load4(addr)
    ))).


End Impl.
