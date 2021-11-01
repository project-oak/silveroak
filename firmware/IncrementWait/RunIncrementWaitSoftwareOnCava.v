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

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

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

Definition put_wait_get_relative_pos :=
  match map.get (snd (fst put_wait_get_compile_result)) (fst IncrementWait.put_wait_get) with
  | Some (_, _, p) => p
  | None => -1111
  end.

Definition all_insts: list Instruction := put_wait_get_asm.

(* Invalid ra, will cause crash (intended), but in real usage, this would be a
   return address pointing into the caller's code. *)
Definition ret_addr: word := word.of_Z (-4).

Section WithVar.
  Instance var : tvar := denote_type.

  Definition initial: ExtraRiscvMachine counter_device := {|
    getMachine := {|
      getRegs := map.put (map.put (map.put
          (map.of_list (List.map (fun n => (Z.of_nat n, word.of_Z 0)) (List.seq 0 32)))
          RegisterNames.sp stack_pastend)
          RegisterNames.a0 (word.of_Z 42))
          RegisterNames.ra ret_addr;
      getPc := word.add code_start (word.of_Z put_wait_get_relative_pos);
      getNextPc := word.add (word.add code_start (word.of_Z put_wait_get_relative_pos))
                            (word.of_Z 4);
      getMem := map.putmany (map.of_list_word_at code_start (Pipeline.instrencode all_insts))
                            (map.of_list_word_at (word.sub stack_pastend (word.of_Z 512))
                                                 (List.repeat Byte.x00 512));
      getXAddrs := List.map (fun n => word.add code_start (word.of_Z (Z.of_nat n)))
                            (List.seq 0 (4 * List.length all_insts));
      getLog := [];
    |};
    getExtraState := reset_state incr;
  |}.

  Definition sched: schedule := fun n => (n mod 2)%nat.

  Definition force_ow(ow: option word): Z :=
    match ow with
    | Some v => word.unsigned v
    | None => -1
    end.

  Definition get_output(m: ExtraRiscvMachine counter_device): Z :=
    force_ow (map.get m.(getRegs) RegisterNames.a0).

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

  Definition res(nsteps: nat): LogElem := outcomeToLogElem (run_rec sched 0 nsteps initial).

  (* We can vm_compute through the execution of the IncrementWait program,
     riscv-coq's processor model, and Cava's reaction to the IncrementWait program: *)
  Goal exists nsteps, res nsteps = (true, word.unsigned ret_addr, 43).
    exists 55%nat. vm_compute. reflexivity.
  Qed.
End WithVar.
