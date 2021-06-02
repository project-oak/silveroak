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

  (* sw/device/lib/base/bitfield.h *)

  (****
     inline uint32_t bitfield_field32_write(uint32_t bitfield,
                                            bitfield_field32_t field,
                                            uint32_t value) {
       bitfield &= ~(field.mask << field.index);
       bitfield |= (value & field.mask) << field.index;
       return bitfield;
     }
   ***)
  Definition bitfield_field32_write : func :=
    let bitfield := "bitfield" in
    let field_mask := "field_mask" in
    let field_index := "field_index" in
    let value := "value" in
    let out := "out" in
    ("b2_bitfield_field32_write", ([bitfield; field_mask; field_index; value],[out],
    bedrock_func_body:(
      (* FIXME no ~ operator *)
      bitfield = bitfield & (field_mask << field_index);
      bitfield = bitfield | ((value & field_mask) << field_index);
      out = bitfield
    ))).

  (****
     inline uint32_t bitfield_field32_read(uint32_t bitfield,
                                           bitfield_field32_t field) {
       return (bitfield >> field.index) & field.mask;
     }
   ***)
  Definition bitfield_field32_read : func :=
    let bitfield := "bitfield" in
    let field_mask := "field_mask" in
    let field_index := "field_index" in
    let out := "out" in
    ("b2_bitfield_field32_read", ([bitfield; field_mask; field_index],[out],
    bedrock_func_body:(
      out = ((bitfield >> field_index) & field_mask)
    ))).

  (****
     inline uint32_t bitfield_bit32_write(uint32_t bitfield,
                                          bitfield_bit32_index_t bit_index,
                                          bool value) {
       return bitfield_field32_write(bitfield, bitfield_bit32_to_field32(bit_index),
                                     value ? 0x1u : 0x0u);
     }
   ***)
  Definition bitfield_bit32_write : func :=
    let bitfield := "bitfield" in
    let bit_index := "bit_index" in
    let value := "value" in
    let out := "out" in
    ("b2_bitfield_bit32_write", ([bitfield; bit_index; value],[out],
    bedrock_func_body:(
      (* FIXME value is boolean, how to handle that? *)
      unpack! out = bitfield_field32_write(bitfield, 1, bit_index, (value==1))
    ))).

  (****
     inline bool bitfield_bit32_read(uint32_t bitfield,
                                     bitfield_bit32_index_t bit_index) {
       return bitfield_field32_read(bitfield,
                                    bitfield_bit32_to_field32(bit_index)) == 0x1u;
     }
   ***)
  Definition bitfield_bit32_read : func :=
    let bitfield := "bitfield" in
    let bit_index := "bit_index" in
    let out := "out" in
    ("b2_bitfield_bit32_read", ([bitfield; bit_index],[out],
    bedrock_func_body:(
      (* FIXME returns boolean *)
      unpack! out = bitfield_field32_read(bitfield, 1, bit_index)
    ))).

End Impl.

