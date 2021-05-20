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
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitMMIO.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require coqutil.Word.Naive.
Require coqutil.Map.SortedListWord.
Require riscv.Utility.InstructionNotations.
Import Syntax.Coercions.
Local Open Scope string_scope.

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

(* dummy base address -- just past end of stack *)
Definition base_addr : Z := 16 * 2^10.
Instance consts : constants Z :=
  {| VALUE_ADDR := base_addr;
     STATUS_ADDR := base_addr + 4;
     STATUS_IDLE := 1;
     STATUS_BUSY := 2;
     STATUS_DONE := 3
  |}.
Existing Instance constant_words.

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

(* use literals for the main function *)
Existing Instance constant_literals.

(* pointers to input and output memory locations *)
Definition input_ptr := base_addr + 8.
Definition output_ptr := base_addr + 12.

(* read input from memory, call put_wait_get, write output to memory *)
Definition main_body : cmd :=
  (* allocate a temporary variable to store output *)
  cmd.stackalloc
    "out" 4
    (cmd.seq
       (* call put_wait_get *)
       (cmd.call ["out"] put_wait_get
                 (globals
                    ++ [expr.load access_size.word (expr.literal input_ptr)]))
       (* store result *)
       (cmd.store access_size.word (expr.literal output_ptr) (expr.var "out"))).

Definition main : func :=
  ("main", ([], [], main_body)).

Definition funcs := [main; put_wait_get].

Derive put_wait_get_compile_result
       SuchThat (compile (map.of_list funcs)
                 = Some put_wait_get_compile_result)
       As put_wait_get_compile_result_eq.
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

Definition put_wait_get_asm := Eval compute in fst (fst put_wait_get_compile_result).

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Redirect "put_wait_get.s" Print put_wait_get_asm.
  (*
    put_wait_get:
     addi    x2, x2, -84   // decrease stack pointer
     sw      x2, x1, 52    // save ra
     sw      x2, x5, 0     // save registers that will be used for temporaries
     sw      x2, x14, 4
     sw      x2, x15, 8
     sw      x2, x16, 12
     sw      x2, x17, 16
     sw      x2, x13, 20
     sw      x2, x12, 24
     sw      x2, x6, 28    // save registers that will be used for arguments
     sw      x2, x7, 32
     sw      x2, x8, 36
     sw      x2, x9, 40
     sw      x2, x10, 44
     sw      x2, x11, 48
     lw      x6, x2, 60    // load arguments
     lw      x7, x2, 64
     lw      x8, x2, 68
     lw      x9, x2, 72
     lw      x10, x2, 76
     lw      x11, x2, 80
     addi    x5, x2, 0     // save stack pointer in register?
     sw      x6, x11, 0    // MMIO write : write value
     addi    x13, x0, 0    // x13 = 0
     addi    x14, x0, 1    // loop start
     sll     x15, x14, x10 // 1 << STATUS_DONE
     and     x16, x13, x15 // x13 & (1 << STATUS_DONE)
     addi    x17, x0, 0
     bne     x16, x17, 12  // if x16 != 0 then break loop
     lw      x13, x7, 0    // MMIO read : read status
     jal     x0, -24       // jump back to loop start
     lw      x12, x6, 0    // MMIO read : read value
     sw      x2, x12, 56   // store return value
     lw      x5, x2, 0     // restore values of temporary registers
     lw      x14, x2, 4
     lw      x15, x2, 8
     lw      x16, x2, 12
     lw      x17, x2, 16
     lw      x13, x2, 20
     lw      x12, x2, 24
     lw      x6, x2, 28    // restore values of argument registers
     lw      x7, x2, 32
     lw      x8, x2, 36
     lw      x9, x2, 40
     lw      x10, x2, 44
     lw      x11, x2, 48
     lw      x1, x2, 52    // load ra
     addi    x2, x2, 84    // increase stack pointer
     jalr    x0, x1, 0     // return


    main:
     addi    x2, x2, -48   // decrease stack pointer
     sw      x2, x1, 44    // save ra
     sw      x2, x5, 4     // save registers that will be used for temporaries
     sw      x2, x7, 8
     sw      x2, x8, 12
     sw      x2, x9, 16
     sw      x2, x10, 20
     sw      x2, x11, 24
     sw      x2, x12, 28
     sw      x2, x13, 32
     sw      x2, x6, 36
     sw      x2, x14, 40
     addi    x5, x2, 4     // save stack pointer+4 in register x5
     addi    x6, x2, 0     // save stack pointer in register x6
     lui     x7, 16384     // compute global constants
     xori    x7, x7, 0
     lui     x8, 16384
     xori    x8, x8, 4
     addi    x9, x0, 1
     addi    x10, x0, 2
     addi    x11, x0, 3
     lui     x12, 16384    // compute input ptr
     xori    x12, x12, 8
     lw      x13, x12, 0   // load input
     sw      x2, x7, -24   // put arguments on stack
     sw      x2, x8, -20
     sw      x2, x9, -16
     sw      x2, x10, -12
     sw      x2, x11, -8
     sw      x2, x13, -4
     jal     x1, -316      // call put_wait_get
     lw      x6, x2, -28   // fetch return value
     lui     x14, 16384    // compute output ptr
     xori    x14, x14, 12
     sw      x14, x6, 0    // store output
     lw      x5, x2, 4     // restore values of temorary registers
     lw      x7, x2, 8
     lw      x8, x2, 12
     lw      x9, x2, 16
     lw      x10, x2, 20
     lw      x11, x2, 24
     lw      x12, x2, 28
     lw      x13, x2, 32
     lw      x6, x2, 36
     lw      x14, x2, 40
     lw      x1, x2, 44    // load ra
     addi    x2, x2, 48    // increase stack pointer
     jalr    x0, x1, 0     // return
   *)
End PrintAssembly.
