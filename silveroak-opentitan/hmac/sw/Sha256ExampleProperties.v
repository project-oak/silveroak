Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Byte.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import HmacSpec.SHA256.
Require Import HmacSoftware.HmacSemantics.
Require Import HmacSoftware.HmacProperties.
Require Import HmacSoftware.Sha256Example.
Import Syntax.Coercions List.ListNotations HList.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Section Proofs.
  Context {word: word.word 32} {mem: map.map word byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {timing: timing}.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (M:=hmac_state_machine)).

  Notation bytearray := (array (mem := mem) ptsto (word.of_Z 1)).

  Definition sha256_post(input_addr: word)(input: list byte)(digest_addr: word)(R: mem -> Prop)
             (tr: trace)(m: mem)(rets: list word): Prop :=
    rets = [] /\
    execution tr (IDLE (sha256 input) (* digest has been read, but still in device *)
                       {| hmac_done := false; (* done flag was already cleared *)
                          intr_enable := word.of_Z 0;
                          hmac_en := false;
                          sha_en := true;
                          swap_endian := true;
                          swap_digest := false; |}) /\
    (* digest has been stored at correct memory location: *)
    (bytearray digest_addr (sha256 input) *
    (* input and rest of memory unmodified: *)
     bytearray input_addr input * R)%sep m.

  Global Instance spec_of_sha256 : spec_of b2_sha256 :=
    fun function_env =>
      forall tr (m: mem) (R : mem -> Prop) (idlebuffer: list byte) (idleconfig: idle_data)
             (input_addr input_len digest_addr: word) (input digest_trash: list byte),
      Z.of_nat (length input) = word.unsigned input_len ->
      Z.of_nat (length digest_trash) = 32 ->
      input_addr <> word.of_Z 0 ->
      digest_addr <> word.of_Z 0 ->
      (bytearray input_addr input * bytearray digest_addr digest_trash * R)%sep m ->
      execution tr (IDLE idlebuffer idleconfig) ->
      call function_env b2_sha256 tr m [digest_addr; input_addr; input_len]
           (sha256_post input_addr input digest_addr R).

  Lemma sha256_correct :
    program_logic_goal_for_function! b2_sha256.
  Proof.
    repeat straightline.
    straightline_call. 1: ecancel_assumption. 1: eassumption.
    repeat straightline.
    straightline_call. 1: symmetry; eassumption. 1: assumption. 1: ecancel_assumption. 1: eassumption.
    repeat straightline.
    straightline_call. 1: eassumption. 1: assumption. 1: ecancel_assumption. 1: eassumption.
    repeat straightline.
    unfold sha256_post.
    split; [reflexivity|]. split; [assumption|].
    rewrite List.app_nil_l in *. ecancel_assumption.
  Qed.
End Proofs.
