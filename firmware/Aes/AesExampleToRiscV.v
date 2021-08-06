Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import bedrock2.Syntax.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.MemoryLayout.
Require Import compiler.Pipeline.
Require Import compiler.RiscvWordProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Aes.Constants.
Require Import Bedrock2Experiments.Aes.Aes.
Require Import Bedrock2Experiments.Aes.AesExample.
Require Import Bedrock2Experiments.Aes.AesToRiscV.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require coqutil.Word.Naive.
Require coqutil.Map.SortedListWord.
Require riscv.Utility.InstructionNotations.
Import Syntax.Coercions.
Local Open Scope string_scope.

(* use literals for the main function *)
Existing Instance constant_literals.

(* pointers to input and output memory locations (these are dummy values) *)
Definition input_data_ptr := AES_BASE_ADDR + 0x70.
Definition input_iv_ptr := AES_BASE_ADDR + 0x80.
Definition input_key_ptr := AES_BASE_ADDR + 0x90.
Definition output_ptr := AES_BASE_ADDR + 0x70.

(* main function: simply call aes_encrypt with literal constants and pointers *)
Definition main_body : cmd :=
  cmd.call []
           aes_encrypt
           [expr.literal input_data_ptr;
           expr.literal input_key_ptr;
           expr.literal input_iv_ptr;
           expr.literal output_ptr].

Definition main : func :=
  ("main", ([], [], main_body)).

Definition funcs : list func := [main; aes_encrypt].

Derive aes_example_compile_result
       SuchThat (compile compile_ext_call (map.of_list (funcs ++ AesToRiscV.funcs))
                 = Some aes_example_compile_result)
       As aes_example_compile_result_eq.
Proof.
  (* doing a more surgical vm_compute in the lhs only avoids fully computing the map
     type, which would slow eq_refl and Qed dramatically *)
  lazymatch goal with
    |- ?lhs = _ =>
    let x := (eval vm_compute in lhs) in
    change lhs with x
  end.
  exact eq_refl.
Qed.

Definition aes_example_asm := Eval compute in fst (fst aes_example_compile_result).

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Redirect "aes_example.s" Print aes_example_asm.
End PrintAssembly.
