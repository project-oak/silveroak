Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import bedrock2.Syntax.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.Pipeline.
Require Import compiler.RiscvWordProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.Hmac.Hmac.
Require Import Bedrock2Experiments.Hmac.Sha256Example.
Require Import Bedrock2Experiments.StateMachineMMIO.

Require coqutil.Word.Naive.
Require coqutil.Map.SortedListWord.
Require riscv.Utility.InstructionNotations.
Import Syntax.Coercions.
Local Open Scope string_scope.

Instance word: word.word 32 := Naive.word 32.
Instance mem: map.map word Byte.byte := SortedListWord.map _ _.
Existing Instance SortedListString.map.
Existing Instance SortedListString.ok.

(* TODO: we actually need a different word implementation than Naive here; in
   corner cases such as a shift argument greater than the width of the word,
   the naive implementation violates the riscv_ok requirements *)
Instance naive_riscv_ok : word.riscv_ok word. Admitted.

Definition heap_start: word := word.of_Z (4*2^10).

(* dummy base address -- just past end of stack *)
Definition base_addr : Z := 16 * 2^10.

(* pointers to input and output memory locations *)
Definition digest_ptr  : Z := word.unsigned heap_start.
Definition msg_ptr     : Z := word.unsigned heap_start + 4.
Definition msg_len_ptr : Z := word.unsigned heap_start + 8.

Definition main_body: cmd := cmd.call [] b2_sha256 [
  expr.load access_size.word (expr.literal digest_ptr);
  expr.load access_size.word (expr.literal msg_ptr);
  expr.load access_size.word (expr.literal msg_len_ptr)
].

Definition main: func := ("main", ([], [], main_body)).

Definition funcs := [
  main; b2_sha256;
  b2_hmac_sha256_init; b2_hmac_sha256_update; b2_hmac_sha256_final;
  abs_mmio_write32; abs_mmio_read32; abs_mmio_write8; abs_mmio_read8;
  bitfield_bit32_write; bitfield_bit32_read;
  bitfield_field32_write; bitfield_field32_read
].

Definition compiler_invocation: option (list Decode.Instruction * (SortedListString.map Z) * Z) :=
  compile compile_ext_call (map.of_list funcs).

Definition sha256_compile_result: list Decode.Instruction * (SortedListString.map Z) * Z.
  let r := eval vm_compute in compiler_invocation in
   match r with
  | Some ?x => exact x
  end.
Defined.

Definition sha256_example_asm := Eval compute in fst (fst sha256_compile_result).

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal False.
    let r := eval unfold sha256_example_asm in sha256_example_asm in idtac (*r*).
  Abort.
End PrintAssembly.
