Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Require Import Bedrock2Experiments.IncrementWait.CavaIncrementDevice.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.InstructionCoercions.
Open Scope ilist_scope.

From Cava Require Import
     Expr
     Semantics
     Types.

Definition code_start    : word := word.of_Z 0.
Definition code_pastend  : word := word.of_Z (4*2^10).
Definition heap_start    : word := word.of_Z (4*2^10).
Definition heap_pastend  : word := word.of_Z (8*2^10).
Definition stack_start   : word := word.of_Z (8*2^10).
Definition stack_pastend : word := word.of_Z (16*2^10).

Definition main_relative_pos :=
  match map.get (snd (fst put_wait_get_compile_result)) (fst main) with
  | Some p => p
  | None => -1111
  end.

Definition p_call: word :=
  word.add code_start (word.of_Z (4 * Z.of_nat (List.length put_wait_get_asm))).

Definition all_insts: list Instruction :=
  put_wait_get_asm ++ [[ Jal RegisterNames.ra
            (main_relative_pos + word.signed (word.sub code_start p_call))]].


Section WithVar.
  Instance var : tvar := denote_type.

  Definition initial: ExtraRiscvMachine counter_device := {|
    getMachine := {|
      getRegs := map.put (map.of_list (List.map (fun n => (Z.of_nat n, word.of_Z 0)) (List.seq 0 32)))
                         RegisterNames.sp stack_pastend;
      getPc := p_call;
      getNextPc := word.add p_call (word.of_Z 4);
      getMem := (map.putmany (map.of_list_word_at code_start (Pipeline.instrencode all_insts))
                (map.putmany (map.of_list_word_at (word.sub stack_pastend (word.of_Z 512))
                                                  (List.repeat Byte.x00 512))
                (map.of_list_word_at heap_start
                          (HList.tuple.to_list (LittleEndian.split 4 42) ++
                           HList.tuple.to_list (LittleEndian.split 4 12345678)))));
      getXAddrs := List.map (fun n => word.add code_start (word.of_Z (Z.of_nat n)))
                            (List.seq 0 (4 * List.length all_insts));
      getLog := [];
    |};
    getExtraState := reset_state incr;
  |}.

  Definition sched: schedule := fun n => (n mod 2)%nat.

  Definition force_ow32(ow32: option Utility.w32): Z :=
    match ow32 with
    | Some v => LittleEndian.combine 4 v
    | None => -1
    end.

  Definition get_output(m: ExtraRiscvMachine counter_device): Z :=
    force_ow32 (Memory.loadWord m.(getMachine).(getMem) (word.of_Z (width:=32) output_ptr)).

  Definition LogElem := (bool * Z * Z)%type. (* (ok-flag, pc, output) triples *)

  Definition outcomeToLogElem(outcome: option unit * ExtraRiscvMachine counter_device): LogElem :=
    (match fst outcome with
     | Some _ => true
     | None => false
     end,
     word.unsigned (snd outcome).(getMachine).(getPc),
     get_output (snd outcome)).

  Fixpoint trace(nsteps: nat)(start: ExtraRiscvMachine counter_device):
    ExtraRiscvMachine counter_device * list LogElem:=
    match nsteps with
    | O => (start, [outcomeToLogElem (Some tt, start)])
    | S n => let (m, t) := trace n start in
             let r := nth_step sched n m in
             (snd r, t ++ [outcomeToLogElem r])
    end%list.

  (* Useful for debugging: display (ok-flag, pc, output) after each cycle:
  Compute snd (trace 100 initial).
  *)

  Definition res(nsteps: nat): LogElem := outcomeToLogElem (run sched nsteps initial).

  (* We can vm_compute through the execution of the IncrementWait program,
     riscv-coq's processor model, and Cava's reaction to the IncrementWait program: *)
  Goal exists nsteps, res nsteps = (true, word.unsigned p_call + 4, 43).
    exists 82%nat. vm_compute. reflexivity.
  Qed.
End WithVar.
