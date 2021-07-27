Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.Hmac.Sha256ToRiscV.
Require Import Bedrock2Experiments.Hmac.CavaHmacDevice.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.InstructionCoercions.
Open Scope ilist_scope.

Definition code_start    : Utility.word := word.of_Z 0.
Definition code_pastend  : Utility.word := word.of_Z (4*2^10).
Definition heap_start    : Utility.word := word.of_Z (4*2^10).
Definition heap_pastend  : Utility.word := word.of_Z (8*2^10).
Definition stack_start   : Utility.word := word.of_Z (8*2^10).
Definition stack_pastend : Utility.word := word.of_Z (16*2^10).

Definition main_relative_pos :=
  match map.get (snd (fst sha256_compile_result)) (fst main) with
  | Some p => p
  | None => -1111
  end.

Definition p_call: Utility.word :=
  word.add code_start (word.of_Z (4 * Z.of_nat (List.length sha256_example_asm))).

Definition all_insts: list Instruction :=
  sha256_example_asm ++ [[ Jal RegisterNames.ra
            (main_relative_pos + word.signed (word.sub code_start p_call))]].

Definition test_msg_str: string := "Hello world".

Definition test_msg: list Byte.byte := Eval compute in list_byte_of_string test_msg_str.

(* obtained with `echo -n "Hello world" | sha256sum *)
Definition expected_output: list Byte.byte := [
  Byte.x64; Byte.xec; Byte.x88; Byte.xca; Byte.x00; Byte.xb2; Byte.x68; Byte.xe5; Byte.xba; Byte.x1a; Byte.x35; Byte.x67; Byte.x8a; Byte.x1b; Byte.x53; Byte.x16; Byte.xd2; Byte.x12; Byte.xf4; Byte.xf3; Byte.x66; Byte.xb2; Byte.x47; Byte.x72; Byte.x32; Byte.x53; Byte.x4a; Byte.x8a; Byte.xec; Byte.xa3; Byte.x7f; Byte.x3c
].

Definition digest_loc  : Z := word.unsigned heap_start + 12.
Definition digest_len  : Z := 256/8.
Definition msg_loc     : Z := digest_loc + digest_len.
Definition msg_len     : Z := Z.of_nat (List.length test_msg).
Definition msg_len_loc : Z := msg_loc + msg_len.

(* just some pattern of the right length, easy to spot while debugging: *)
Definition initial_data_at_digest: list Byte.byte :=
  [Byte.xaa] ++ (List.repeat Byte.xbb (Z.to_nat digest_len - 2)) ++ [Byte.xcc].

Definition initial_def: ExtraRiscvMachine hmac_device := {|
  getMachine := {|
    getRegs := map.put (map.of_list (List.map (fun n => (Z.of_nat n, word.of_Z 0)) (List.seq 0 32)))
                       RegisterNames.sp stack_pastend;
    getPc := p_call;
    getNextPc := word.add p_call (word.of_Z 4);
    getMem := (map.putmany (map.of_list_word_at code_start (Pipeline.instrencode all_insts))
              (map.putmany (map.of_list_word_at (word.sub stack_pastend (word.of_Z 512))
                                                (List.repeat Byte.x00 512))
              (map.of_list_word_at heap_start
                        (HList.tuple.to_list (LittleEndian.split 4 digest_loc) ++
                         HList.tuple.to_list (LittleEndian.split 4 msg_loc) ++
                         HList.tuple.to_list (LittleEndian.split 4 msg_len_loc) ++
                         initial_data_at_digest ++
                         test_msg ++
                         HList.tuple.to_list (LittleEndian.split 4 msg_len)))));
    getXAddrs := List.map (fun n => word.add code_start (word.of_Z (Z.of_nat n)))
                          (List.seq 0 (4 * List.length all_insts));
    getLog := [];
  |};
  getExtraState := tt; (* TODO replace by reset_state *)
|}.

Definition initial := Eval vm_compute in initial_def. (* takes a few seconds *)

Definition sched: schedule := fun n => (n mod 2)%nat.

Definition force_olist{A: Type}(ol: option (list A)): list A :=
  match ol with
  | Some l => l
  | None => []
  end.

Definition get_output(m: ExtraRiscvMachine hmac_device): list Byte.byte :=
  let addrs := List.unfoldn (word.add (word.of_Z 1))
                            (Z.to_nat digest_len)
                            (word.of_Z (width := 32) digest_loc) in
  force_olist (map.getmany_of_list m.(getMachine).(getMem) addrs).

Definition LogElem := (bool * Z * list Byte.byte)%type. (* (ok-flag, pc, output) triples *)

Definition outcomeToLogElem(outcome: option unit * ExtraRiscvMachine hmac_device): LogElem :=
  (match fst outcome with
   | Some _ => true
   | None => false
   end,
   word.unsigned (snd outcome).(getMachine).(getPc),
   get_output (snd outcome)).

Fixpoint trace(nsteps: nat)(start: ExtraRiscvMachine hmac_device):
  ExtraRiscvMachine hmac_device * list LogElem:=
  match nsteps with
  | O => (start, [outcomeToLogElem (Some tt, start)])
  | S n => let (m, t) := trace n start in
           let r := nth_step sched n m in
           (snd r, t ++ [outcomeToLogElem r])
  end.

(* Useful for debugging: displays the position of each function:
Compute (snd (fst sha256_compile_result)).
*)

(* Useful for debugging: display (ok-flag, pc, output) after each cycle:
Compute snd (trace 50 initial).
*)

Definition res(nsteps: nat): LogElem := outcomeToLogElem (run sched nsteps initial).

Goal exists nsteps, res nsteps = (true, word.unsigned p_call + 4, expected_output).
  (* wrong number of steps, and doesn't work currently because Cava Hmac device is not yet
     hooked up, and probably there are also bugs in the Hmac driver code and in the current file *)
  exists 20%nat. vm_compute. (* `reflexivity` is supposed to work here eventually *)
Abort.
