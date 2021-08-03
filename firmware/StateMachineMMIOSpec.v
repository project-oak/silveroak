(* This instance sits at the interface between the StateMachineMMIO compiler
   and the MMIOToCava proof, and since neither should import the other, we
   put this instance in a separate file. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import riscv.Utility.Utility.
Require Import Bedrock2Experiments.Riscv.MinimalMMIO.
Require Import Bedrock2Experiments.Riscv.MetricMinimalMMIO.
Require Import Bedrock2Experiments.ProgramSemantics32.
Require Import Bedrock2Experiments.StateMachineSemantics.

Instance StateMachineMMIOSpec{word: word.word 32}{mem: map.map word Byte.byte}
         {M: state_machine.parameters}: MMIOSpec :=
  {  isMMIOAddr := state_machine.isMMIOAddr;
     isMMIOAligned n a := word.unsigned a mod (Z.of_nat n) = 0;
     MMIOReadOK :=
       fun sz log addr val =>
         exists s s' r,
           execution log s
           /\ state_machine.reg_addr r = addr
           /\ state_machine.read_step sz s r val s';
     MMIOWriteOK :=
       fun sz log addr val =>
         exists s s' r,
           execution log s
           /\ state_machine.reg_addr r = addr
           /\ state_machine.write_step sz s r val s';
  }.

Section TODO_Why_not_like_this. (* (would also require a corresponding update in ext_spec) *)
  Instance StateMachineMMIOSpec_Alt{word: word.word 32}{mem: map.map word Byte.byte}
           {M: state_machine.parameters}: MMIOSpec :=
    {| isMMIOAddr := state_machine.isMMIOAddr;
       isMMIOAligned n a := word.unsigned a mod (Z.of_nat n) = 0;
       MMIOReadOK :=
         fun sz log addr val =>
           exists r, state_machine.reg_addr r = addr /\
                     (* for all states s that could be the explanation of the trace t,
                        this read_step must be possible *)
                     forall s, execution log s -> exists s', state_machine.read_step sz s r val s';
       MMIOWriteOK :=
         fun sz log addr val =>
           exists r, state_machine.reg_addr r = addr /\
                     (* for all states s that could be the explanation of the trace t,
                        this write_step must be possible *)
                     forall s, execution log s -> exists s', state_machine.write_step sz s r val s';
    |}.
End TODO_Why_not_like_this.
