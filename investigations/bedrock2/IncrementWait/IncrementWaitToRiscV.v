Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.MemoryLayout.
Require Import compiler.PipelineWithRename.
Require Import compiler.RiscvWordProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitMMIO.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require coqutil.Word.Naive.
Require coqutil.Map.SortedListWord.
Require riscv.Utility.InstructionNotations.

(* TODO: we actually need a different word implementation than Naive here; in
   corner cases such as a shift argument greater than the width of the word,
   the naive implementation violates the riscv_ok requirements *)
Axiom naive_riscv_ok : word.riscv_ok (Naive.word 32).
Instance p : MMIO.parameters :=
  {| MMIO.word := Naive.word 32;
     MMIO.word_ok := Naive.word32_ok;
     MMIO.word_riscv_ok := naive_riscv_ok;
     MMIO.mem := SortedListWord.map _ _;
     MMIO.mem_ok := _;
     MMIO.locals := Zkeyed_map _;
     MMIO.locals_ok := Zkeyed_map_ok _;
     MMIO.funname_env := SortedListString.map;
     MMIO.funname_env_ok := SortedListString.ok;
  |}.

Existing Instances Words32 semantics_params semantics_params_ok compilation_params IncrementWaitMMIOSpec FlatToRiscv_params.

Definition ml: MemoryLayout := {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (4*2^10);
  MemoryLayout.heap_start    := word.of_Z (4*2^10);
  MemoryLayout.heap_pastend  := word.of_Z (8*2^10);
  MemoryLayout.stack_start   := word.of_Z (8*2^10);
  MemoryLayout.stack_pastend := word.of_Z (16*2^10);
                              |}.

Definition base_addr := word.add (MemoryLayout.stack_pastend ml) (word.of_Z 400).
Instance consts : constants MMIO.word :=
  {| VALUE_ADDR := base_addr;
     STATUS_ADDR := word.add base_addr (word.of_Z 4);
     STATUS_IDLE := word.of_Z 1;
     STATUS_BUSY := word.of_Z 2;
     STATUS_DONE := word.of_Z 3
  |}.

Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

Instance pipeline_params : Pipeline.parameters :=
  {|
  Pipeline.W := Words32;
  Pipeline.mem := _;
  Pipeline.Registers := _;
  Pipeline.string_keyed_map := _;
  Pipeline.ext_spec := @FlatToRiscvCommon.ext_spec FlatToRiscv_params;
  Pipeline.compile_ext_call := (@FlatToRiscvDef.compile_ext_call compilation_params);
  Pipeline.M := _;
  Pipeline.MM := _;
  Pipeline.RVM := MetricMinimalMMIO.IsRiscvMachine;
  Pipeline.PRParams := @FlatToRiscvCommon.PRParams FlatToRiscv_params
  |}.

Definition funcs := [put_wait_get].
Derive put_wait_get_asm
       SuchThat (exists env,
                    compile ml (map.putmany_of_list funcs map.empty) = Some (put_wait_get_asm,env))
       As compile_put_wait_get.
Proof.
  eexists.
  (* doing a more surgical vm_compute in the lhs only avoids fully computing the map
     type, which would slow eq_refl and Qed dramatically *)
  lazymatch goal with
    |- ?lhs = _ =>
    let x := (eval vm_compute in lhs) in
    change lhs with x
  end.
  exact eq_refl.
Qed.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  (* Uncomment to see assembly code *)
  (* Print put_wait_get_asm. *)
End PrintAssembly.
