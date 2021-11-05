Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import HmacHardware.Hmac.
Require Import HmacSoftware.Sha256ToRiscV.
Require Import HmacEnd2End.CavaHmacDevice.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.InstructionCoercions.
Require Import Cava.Expr.
Require Import Cava.Semantics.
Require Import Cava.Types.

Open Scope ilist_scope.

Definition test_msg_str: string := "Hello world".

Definition test_msg: list Byte.byte := Eval compute in list_byte_of_string test_msg_str.

(* obtained with `echo -n "Hello world" | sha256sum *)
Definition expected_output: list Byte.byte := [
  Byte.x64; Byte.xec; Byte.x88; Byte.xca; Byte.x00; Byte.xb2; Byte.x68; Byte.xe5; Byte.xba; Byte.x1a; Byte.x35; Byte.x67; Byte.x8a; Byte.x1b; Byte.x53; Byte.x16; Byte.xd2; Byte.x12; Byte.xf4; Byte.xf3; Byte.x66; Byte.xb2; Byte.x47; Byte.x72; Byte.x32; Byte.x53; Byte.x4a; Byte.x8a; Byte.xec; Byte.xa3; Byte.x7f; Byte.x3c
].

Definition code_start    : word := word.of_Z 0.
Definition code_pastend  : word := word.of_Z (4*2^10).
Definition heap_start    : word := word.of_Z (4*2^10).
Definition heap_pastend  : word := word.of_Z (8*2^10).
Definition stack_start   : word := word.of_Z (8*2^10).
Definition stack_pastend : word := word.of_Z (16*2^10).

Definition digest_loc  : Z := word.unsigned heap_start.
Definition digest_len  : Z := 256/8.
Definition msg_loc     : Z := digest_loc + digest_len.
Definition msg_len     : Z := Z.of_nat (List.length test_msg).

(* just some pattern of the right length, easy to spot while debugging: *)
Definition initial_data_at_digest: list Byte.byte :=
  [Byte.xaa] ++ (List.repeat Byte.xbb (Z.to_nat digest_len - 2)) ++ [Byte.xcc].

(* Invalid ra, will cause crash (intended), but in real usage, this would be a
   return address pointing into the caller's code. *)
Definition ret_addr: word := word.of_Z (-4).

Definition initial_def: ExtraRiscvMachine hmac_device := {|
  getMachine := {|
    getRegs := map.put (map.put (map.put (map.put (map.put
      (map.of_list (List.map (fun n => (Z.of_nat n, word.of_Z 0)) (List.seq 0 32)))
      RegisterNames.sp stack_pastend)
      RegisterNames.a0 (word.of_Z digest_loc))
      RegisterNames.a1 (word.of_Z msg_loc))
      RegisterNames.a2 (word.of_Z msg_len))
      RegisterNames.ra ret_addr;
    getPc := word.add code_start (word.of_Z sha256_relative_pos);
    getNextPc := word.add (word.add code_start (word.of_Z sha256_relative_pos)) (word.of_Z 4);
    getMem := (map.putmany (map.of_list_word_at code_start (Pipeline.instrencode sha256_asm))
              (map.putmany (map.of_list_word_at (word.sub stack_pastend (word.of_Z 512))
                                                (List.repeat Byte.x00 512))
              (map.of_list_word_at heap_start (initial_data_at_digest ++ test_msg))));
    getXAddrs := List.map (fun n => word.add code_start (word.of_Z (Z.of_nat n)))
                          (List.seq 0 (4 * List.length sha256_asm));
    getLog := [];
  |};
  getExtraState := reset_state hmac_top;
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

Definition res(nsteps: nat): LogElem := outcomeToLogElem (run_rec sched 0 nsteps initial).

Goal exists nsteps, res nsteps = (true, word.unsigned ret_addr, expected_output).
  (* wrong number of steps, and doesn't work currently because Cava Hmac device is not yet
     hooked up, and probably there are also bugs in the Hmac driver code and in the current file *)
  exists 20%nat. vm_compute. (* `reflexivity` is supposed to work here eventually *)
Abort.
