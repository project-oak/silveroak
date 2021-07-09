Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import bedrock2.Syntax.
Require Import compiler.FlatToRiscvDef.
Require Export compiler.MemoryLayout.
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
Require Import Bedrock2Experiments.Aes.AesSemantics.
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

Definition ml: MemoryLayout := {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (4*2^10);
  MemoryLayout.heap_start    := word.of_Z (4*2^10);
  MemoryLayout.heap_pastend  := word.of_Z (8*2^10);
  MemoryLayout.stack_start   := word.of_Z (8*2^10);
  MemoryLayout.stack_pastend := word.of_Z (16*2^10);
                              |}.

(* Magic number for aes base address found in
   third_party/opentitan/hw/top_earlgrey/sw/autogen/top_earlgrey.h:

   #define TOP_EARLGREY_AES_BASE_ADDR 0x40110000u *)
Definition AES_BASE_ADDR : Z := 0x40110000.

Local Infix "<<" := Z.shiftl (at level 40) : Z_scope.
Instance consts : aes_constants Z :=
  {|
  (**** Constants from aes_regs.h ****)

  (* #define AES_KEY0(id) (AES##id##_BASE_ADDR + 0x0) *)
  AES_KEY00 := AES_BASE_ADDR + 0x0;

  (* #define AES_IV0(id) (AES##id##_BASE_ADDR + 0x20) *)
  AES_IV00 := AES_BASE_ADDR + 0x20;

  (* #define AES_DATA_IN0(id) (AES##id##_BASE_ADDR + 0x30) *)
  AES_DATA_IN00 := AES_BASE_ADDR + 0x30;

  (* #define AES_DATA_OUT0(id) (AES##id##_BASE_ADDR + 0x40) *)
  AES_DATA_OUT00 := AES_BASE_ADDR + 0x40;

  (* #define AES_CTRL(id) (AES##id##_BASE_ADDR + 0x50) *)
  AES_CTRL0 := AES_BASE_ADDR + 0x50;

  (* #define AES_CTRL_REG_OFFSET 0x50
     #define AES_CTRL_OPERATION 0
     #define AES_CTRL_MODE_MASK 0x7
     #define AES_CTRL_MODE_OFFSET 1
     #define AES_CTRL_KEY_LEN_MASK 0x7
     #define AES_CTRL_KEY_LEN_OFFSET 4
     #define AES_CTRL_MANUAL_OPERATION 7 *)
  AES_CTRL_OPERATION := 0;
  AES_CTRL_MODE_MASK := 0x7;
  AES_CTRL_MODE_OFFSET := 1;
  AES_CTRL_KEY_LEN_MASK := 0x7;
  AES_CTRL_KEY_LEN_OFFSET := 4;
  AES_CTRL_MANUAL_OPERATION := 7;

  (* #define AES_STATUS(id) (AES##id##_BASE_ADDR + 0x58) *)
  AES_STATUS0 := AES_BASE_ADDR + 0x58;

  (* #define AES_STATUS_IDLE 0
     #define AES_STATUS_STALL 1
     #define AES_STATUS_OUTPUT_VALID 2
     #define AES_STATUS_INPUT_READY 3 *)
  AES_STATUS_IDLE := 0;
  AES_STATUS_STALL := 1;
  AES_STATUS_OUTPUT_VALID := 2;
  AES_STATUS_INPUT_READY := 3;

  (* #define AES_PARAM_NUMREGSKEY 8 *)
  AES_NUM_REGS_KEY := 8;

  (* #define AES_PARAM_NUMREGSIV 4 *)
  AES_NUM_REGS_IV := 4;

  (* #define AES_PARAM_NUMREGSDATA 4 *)
  AES_NUM_REGS_DATA := 4;

  (**** Enums from aes.h ****)

  (* typedef enum aes_op { kAesEnc = 0, kAesDec = 1 } aes_op_t; *)
  kAesEnc := 0;
  kAesDec := 1;

  (* typedef enum aes_mode {
       kAesEcb = 1 << 0,
       kAesCbc = 1 << 1,
       kAesCtr = 1 << 2
     } aes_mode_t; *)
  kAesEcb := 1 << 0;
  kAesCbc := 1 << 1;
  kAesCtr := 1 << 2;

  (* typedef enum aes_key_len {
       kAes128 = 1 << 0,
       kAes192 = 1 << 1,
       kAes256 = 1 << 2
     } aes_key_len_t; *)
  kAes128 := 1 << 0;
  kAes192 := 1 << 1;
  kAes256 := 1 << 2;

  |}.

Instance aes_timing : timing := {| timing.ndelays_core := 14%nat |}.

(* TODO: fill in with real circuit spec *)
Axiom aes_spec
  : bool ->
    MMIO.word * MMIO.word * MMIO.word * MMIO.word * MMIO.word * MMIO.word * MMIO.word * MMIO.word ->
    MMIO.word * MMIO.word * MMIO.word * MMIO.word -> MMIO.word * MMIO.word * MMIO.word * MMIO.word ->
    MMIO.word * MMIO.word * MMIO.word * MMIO.word.

Instance aes_parameters : AesSemantics.parameters.parameters :=
  {| AesSemantics.parameters.word := MMIO.word;
     AesSemantics.parameters.mem := MMIO.mem;
     AesSemantics.parameters.aes_spec := aes_spec;
  |}.

Instance aes_parameters_ok : AesSemantics.parameters.ok aes_parameters :=
  {| AesSemantics.parameters.word_ok := MMIO.word_ok;
     AesSemantics.parameters.mem_ok := MMIO.mem_ok;
  |}.

Existing Instances Words32 semantics_parameters StateMachineSemantics.ok state_machine_parameters
         compilation_params StateMachineMMIOSpec FlatToRiscv_params constant_literals.

(* add a stronger hint for state_machine_parameters *)
Local Hint Extern 1 (StateMachineSemantics.parameters _ _ _) =>
exact state_machine_parameters : typeclass_instances.

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

Definition funcs := [aes_data_put_wait
                     ; aes_data_get_wait
                     ; aes_init
                     ; aes_key_put
                     ; aes_iv_put
                     ; aes_data_put
                     ; aes_data_get
                     ; aes_data_ready
                     ; aes_data_valid
                     ; aes_idle].

Derive aes_compile_result
       SuchThat (compile (map.of_list funcs)
                 = Some aes_compile_result)
       As aes_compile_result_eq.
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

Definition aes_asm := Eval compute in fst (fst aes_compile_result).

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Redirect "aes.s" Print aes_asm.
End PrintAssembly.
