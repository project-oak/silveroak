Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import bedrock2.ZnWords.
Require Import compiler.SeparationLogic.
Require Import compiler.LowerPipeline.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import HmacEnd2End.CavaHmacDevice.
Require Import HmacSoftware.Sha256ToRiscV.
Require Import HmacSpec.SHA256.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.Bedrock2ToCava.

Definition binary: list byte := Eval compute in Pipeline.instrencode sha256_asm.

Definition mach_valid(imem: mem -> Prop)(mach: ExtraRiscvMachine hmac_device): Prop :=
  subset (footpr imem) (of_list (getXAddrs mach)) /\
  getNextPc mach = word.add (getPc mach) (word.of_Z 4) /\
  regs_initialized (getRegs mach) /\
  map.undef_on (getMem mach) device.isMMIOAddr /\
  disjoint (of_list (getXAddrs mach)) device.isMMIOAddr.

Local Notation "a * b" := (sep a b) : type_scope.
Local Notation "a * b" := (sep a b).

Add Ring wring : (Properties.word.ring_theory (word := word))
                   (preprocess [autorewrite with rew_word_morphism],
                    morphism (Properties.word.ring_morph (word := word)),
                    constants [Properties.word_cst]).

Declare Scope word_scope.
Infix "+" := word.add : word_scope.
Infix "-" := word.sub : word_scope.
Delimit Scope word_scope with word.
Local Open Scope word_scope.

Notation ShaDevice := hmac_device.

(* Trying to keep toplevel theorem at 53 chars wide:
01234567890123456789012345678901234567890123456789012 *)

Axiom sha256_len: forall inp, List.length (sha256 inp) = 32%nat.

Theorem sha256_end2end_correct:
forall a_outp a_inp len sp_val a_ret a_code stack_lo
  (inp: list byte) (Rdata Rexec: mem->Prop)
  (sched: nat->nat) (m: ExtraRiscvMachine ShaDevice),
map.get m.(getRegs) RegisterNames.a0 = Some a_outp ->
map.get m.(getRegs) RegisterNames.a1 = Some a_inp ->
map.get m.(getRegs) RegisterNames.a2 = Some len ->
map.get m.(getRegs) RegisterNames.sp = Some sp_val ->
map.get m.(getRegs) RegisterNames.ra = Some a_ret ->
m.(getPc) = a_code ->
Z.of_nat (length inp) = word.unsigned len ->
a_inp <> word.of_Z 0 ->
a_outp <> word.of_Z 0 ->
256 <= word.unsigned (sp_val - stack_lo) ->
word.unsigned (sp_val - stack_lo) mod 4 = 0 ->
word.unsigned a_code mod 4 = 0 ->
word.unsigned a_ret mod 4 = 0 ->
device.is_ready_state m.(getExtraState) ->
mach_valid (ptsto_bytes a_code binary * Rexec) m ->
(bytearray a_inp inp *
 mem_available a_outp (a_outp + (word.of_Z 32)) *
 mem_available stack_lo sp_val * Rdata *
 ptsto_bytes a_code binary * Rexec) m.(getMem) ->
exists n m',
run sched n m = Some m' /\
map.get m'.(getRegs) RegisterNames.sp = Some sp_val /\
map.agree_on callee_saved m.(getRegs) m'.(getRegs) /\
m'.(getPc) = a_ret /\
device.is_ready_state m'.(getExtraState) /\
mach_valid (ptsto_bytes a_code binary * Rexec) m' /\
(bytearray a_inp inp *
 bytearray a_outp (sha256 inp)  *
 mem_available stack_lo sp_val * Rdata *
 ptsto_bytes a_code binary * Rexec) m'.(getMem).
Proof.
  intros.
  change binary with (Pipeline.instrencode sha256_asm).
  assert (((mem_available a_outp (a_outp + (word.of_Z 32)) * bytearray a_inp inp) *
           (mem_available stack_lo sp_val * ptsto_bytes a_code binary * Rexec * Rdata))
            m.(getMem)) as M by ecancel_assumption.
  unfold sep in M at 1. destruct M as (mH & mL & Sp & MH & ML).
  eapply mem_available_to_exists in MH.
  destruct MH as (output_placeholder & HLen & MH).
  ring_simplify (a_outp + word.of_Z 32 - a_outp) in HLen.
  edestruct bedrock2_and_cava_system_correct with
      (f_entry_name := "b2_sha256") (p_functions := a_code)
      (stack_start := stack_lo) (stack_pastend := sp_val)
      (postH := fun mH' (retvals: list word) =>
                  (bytearray a_inp inp * bytearray a_outp (sha256 inp)) mH')
    as (steps_remaining & finalL & mH' & retvals & Rn & GM & A & Eq & M & HP);
    lazymatch goal with
    | |- _ mod _ = _ => idtac
    | |- _ => try eassumption
    end.
  { exact funcs_valid. }
  { apply List.dedup_NoDup_iff. reflexivity. }
  { exact sha256_compile_result_eq. }
  { exact sha256_asm_valid_instructions. }
  { reflexivity. }
  { change sha256_req_stack with (sha256_req_stack * 4 / 4).
    eapply Z.div_le_mono. 1: reflexivity.
    etransitivity. 2: eassumption.
    vm_compute. discriminate. }
  { assumption. }
  { assumption. }
  { assumption. }
  { (* Note: Conveniently, since "b2_sha256" is last in the alphabet among all used functional
       names, sha256_relative_pos equals 0, so the theorem becomes simpler (just jump to a_code
       instead of (a_code+sha256_relative_pos)).
       Compute sha256_finfo. *)
    replace (getPc m) with a_code. symmetry. apply add_0_r. }
  { eapply WeakestPreconditionProperties.Proper_call.
    2: eapply link_sha256.
    6: { instantiate (4 := a_outp). instantiate (5 := a_inp). instantiate (1 := mH).
         unfold ptsto_bytes in *. ecancel_assumption. }
    6: { cbn. instantiate (1 := List.repeat Byte.x00 32). reflexivity. }
    all: try eassumption.
    unfold Morphisms.pointwise_relation, Basics.impl, Sha256ExampleProperties.sha256_post.
    intros. fwd.
    split. 1: ecancel_assumption.
    eexists. split. 1: eassumption. cbn.
    apply sha256_len. }
  { cbn -[map.get].
    repeat match goal with
           | |- context[match ?x with _ => _ end] =>
             match goal with
             | H: ?x' = Some ?y |- _ => replace x with (Some y) by (symmetry; exact H)
             end
           end.
    reflexivity. }
  { unfold machine_ok, mach_valid in *. fwd.
    ssplit; try eassumption.
    change (Pipeline.instrencode sha256_asm) with binary.
    apply sep_comm.
    unfold sep at 1. exists mH, mL. split. 1: exact Sp. split. 1: reflexivity.
    ecancel_assumption. }
  { unfold machine_ok in M. unfold mach_valid. fwd.
    do 2 eexists. ssplit.
    - unfold run. rewrite Rn. reflexivity.
    - assumption.
    - assumption.
    - reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - unfold sep at 1 in Mp0. destruct Mp0 as (mL' & mH'' & Sp' & ML' & ?).  subst mH''.
      enough (((bytearray a_inp inp * bytearray a_outp (sha256 inp)) *
              (mem_available stack_lo sp_val * Rdata *
               ptsto_bytes (getPc m) (Pipeline.instrencode sha256_asm) * Rexec)) (getMem finalL))
        by ecancel_assumption.
      apply sep_comm.
      unfold sep at 1.
      exists mL', mH'. split. 1: exact Sp'. split. 2: exact HP.
      ecancel_assumption. }
  Unshelve.
  all: repeat constructor.
  all: try exact (word.of_Z 0).
Qed.

(* Goal: bring this list down to only standard axioms like functional and propositional extensionality
Print Assumptions sha256_end2end_correct.
 *)
