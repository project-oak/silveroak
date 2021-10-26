Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.Pipeline.
Require Import compiler.RiscvWordProperties.
Require Import Bedrock2Experiments.List.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.AbsMMIOPropertiesUnique.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.LibBase.BitfieldProperties.
Require Import HmacSoftware.Hmac.
Require Import HmacSoftware.HmacSemantics.
Require Import HmacSoftware.HmacProperties.
Require Import HmacSoftware.Sha256Example.
Require Import HmacSoftware.Sha256ExampleProperties.
Require Import Bedrock2Experiments.StateMachineSemantics.
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

(* TODO match to actual Cava implementation *)
Instance hmac_timing: timing := {
  max_negative_done_polls := 16;
}.

Notation bytearray := (bedrock2.Array.array (mem := mem) ptsto (word.of_Z 1)).

(* Plug in the right state machine parameters; typeclass inference struggles here *)
Local Notation execution := (execution (M:=hmac_state_machine)).

Definition funcs := [
  b2_sha256;
  b2_hmac_sha256_init; b2_hmac_sha256_update; b2_hmac_sha256_final;
  abs_mmio_write32; abs_mmio_read32; abs_mmio_write8; abs_mmio_read8;
  bitfield_bit32_write; bitfield_bit32_read;
  bitfield_field32_write; bitfield_field32_read
].

Lemma link_sha256: spec_of_sha256 funcs.
Proof.
  (* TODO speedup, don't reprove the same specs many times *)
  repeat first
         [ eapply sha256_correct
         | eapply hmac_sha256_init_correct
         | eapply hmac_sha256_update_correct
         | eapply hmac_sha256_final_correct
         | eapply abs_mmio_write32_correct
         | eapply abs_mmio_read32_correct
         | eapply abs_mmio_write8_correct
         | eapply abs_mmio_read8_correct
         | eapply bitfield_bit32_write_correct
         | eapply bitfield_field32_write_correct
         | eapply bitfield_bit32_read_correct
         | eapply bitfield_field32_read_correct
         | eapply HmacProperties.execution_unique
         | idtac ].
Qed.

Lemma funcs_valid: ExprImp.valid_funs (map.of_list funcs).
Proof.
  cbv [funcs map.of_list ExprImp.valid_funs]. intros *.
  repeat match goal with
         | |- context[match ?p with _ => _ end] => cbv [p]
         end.
  rewrite !map.get_put_dec, map.get_empty.
  repeat destruct_one_match; inversion 1; cbv [ExprImp.valid_fun].
  all:ssplit.
  all:apply dedup_NoDup_iff.
  all:reflexivity.
Qed.

Definition sha256_compile_result:
  list Decode.Instruction * (SortedListString.map (nat * nat * Z)) * Z.
  let r := eval vm_compute in (compile compile_ext_call (map.of_list funcs)) in
   match r with
  | Some ?x => exact x
  end.
Defined.

Definition sha256_asm := Eval compute in fst (fst sha256_compile_result).
Definition sha256_finfo := Eval compute in snd (fst sha256_compile_result).
Definition sha256_req_stack := Eval compute in snd sha256_compile_result.

Lemma sha256_compile_result_eq:
  compile compile_ext_call (map.of_list funcs) =
  Some (sha256_asm, sha256_finfo, sha256_req_stack).
Proof. reflexivity. Qed.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal False.
    let r := eval unfold sha256_asm in sha256_asm in idtac (*r*).
  Abort.
End PrintAssembly.

Definition sha256_relative_pos :=
  match map.get sha256_finfo (fst b2_sha256) with
  | Some (_, _, p) => p
  | None => -1111
  end.
