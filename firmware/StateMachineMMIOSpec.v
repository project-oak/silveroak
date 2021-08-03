(* This instance sits at the interface between the StateMachineMMIO compiler
   and the MMIOToCava proof, and since neither should import the other, we
   put this instance in a separate file. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import riscv.Utility.Utility.
Require Import Bedrock2Experiments.Riscv.MinimalMMIO.
Require Import Bedrock2Experiments.Riscv.MetricMinimalMMIO.
Require Import Bedrock2Experiments.StateMachineSemantics.

Instance StateMachineMMIOSpec{W: Words}{mem: map.map word byte}
         {parameters: StateMachineSemantics.parameters width word mem}: MMIOSpec :=
  {| isMMIOAddr := parameters.isMMIOAddr;
     isMMIOAligned n a := word.unsigned a mod (Z.of_nat n) = 0;
     MMIOReadOK :=
       fun sz log addr val =>
         exists s s' r,
           execution log s
           /\ parameters.reg_addr r = addr
           /\ parameters.read_step sz s r val s';
     MMIOWriteOK :=
       fun sz log addr val =>
         exists s s' r,
           execution log s
           /\ parameters.reg_addr r = addr
           /\ parameters.write_step sz s r val s';
  |}.

Section TODO_Why_not_like_this. (* (would also require a corresponding update in ext_spec) *)
  Instance StateMachineMMIOSpec_Alt{W: Words}{mem: map.map word byte}
           {parameters: StateMachineSemantics.parameters width word mem}: MMIOSpec :=
    {| isMMIOAddr := parameters.isMMIOAddr;
       isMMIOAligned n a := word.unsigned a mod (Z.of_nat n) = 0;
       MMIOReadOK :=
         fun sz log addr val =>
           exists r, parameters.reg_addr r = addr /\
                     (* for all states s that could be the explanation of the trace t,
                        this read_step must be possible *)
                     forall s, execution log s -> exists s', parameters.read_step sz s r val s';
       MMIOWriteOK :=
         fun sz log addr val =>
           exists r, parameters.reg_addr r = addr /\
                     (* for all states s that could be the explanation of the trace t,
                        this write_step must be possible *)
                     forall s, execution log s -> exists s', parameters.write_step sz s r val s';
    |}.
End TODO_Why_not_like_this.
