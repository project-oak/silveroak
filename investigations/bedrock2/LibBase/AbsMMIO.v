Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Note: these functions are *not* exported to C, because they only
   contain one MMIO call, which is modeled differently in C and bedrock2:
   In C, it's a volatile memory access, whereas in bedrock2, it's an
   external call. *)
Section Impl.
  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).

  (* opentitan/sw/device/silicon_creator/lib/base/abs_mmio.h *)

  (****
     inline void abs_mmio_write8(uint32_t addr, uint8_t value) {
       *(( volatile uint8_t * )addr) = value;
     }
   ***)
  Definition abs_mmio_write8 : func :=
    let addr := "addr" in
    let value := "value" in
    ("abs_mmio_write8", ([addr; value],[],
    bedrock_func_body:(
      output! WRITE8 (addr, value)
    ))).

  (****
     inline uint8_t abs_mmio_read8(uint32_t addr) {
       return *(( volatile uint8_t * )addr);
     }
   ***)
  Definition abs_mmio_read8 : func :=
    let addr := "addr" in
    let out := "out" in
    ("abs_mmio_read8", ([addr],[out],
    bedrock_func_body:(
      io! out = READ8 (addr)
    ))).

  (****
     inline void abs_mmio_write32(uint32_t addr, uint32_t value) {
       *((volatile uint32_t * )addr) = value;
     }
   ***)
  Definition abs_mmio_write32 : func :=
    let addr := "addr" in
    let value := "value" in
    ("abs_mmio_write32", ([addr; value],[],
    bedrock_func_body:(
      output! WRITE32 (addr, value)
    ))).

  (****
     inline uint32_t abs_mmio_read32(uint32_t addr) {
       return *((volatile uint32_t * )addr);
     }
  ***)
  Definition abs_mmio_read32 : func :=
    let addr := "addr" in
    let out := "out" in
    ("abs_mmio_read32", ([addr],[out],
    bedrock_func_body:(
      io! out = READ32 (addr)
    ))).


End Impl.
