Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Import ListNotations.
Local Open Scope Z_scope.

(**** Helpers for working with words ****)

Section WithWord.
  Context {width} {word : word.word width} {word_ok : word.ok word}.

  Definition unique_words (l : list word.rep) : Prop :=
    List.dedup word.eqb l = l.

  (* Compute sequential register addresses given a start address and a number of
   registers *)
  Definition list_reg_addrs (start : word.rep)
             (nregs : nat) (size_in_bytes : Z)
    : list word.rep :=
    map (fun i => word.add start (word.of_Z (Z.of_nat i * size_in_bytes)))
        (seq 0 nregs).

  Definition select_bits (w : word) (offset mask : word) : word :=
    word.and (word.sru w offset) mask.

  (* the flag is set if ((val & (1 << flag)) != 0) *)
  Definition is_flag_set (val : word) (flag : word) : bool :=
    negb (word.eqb (word.and val (word.slu (word.of_Z 1) flag)) (word.of_Z 0)).

  Definition has_size w (n : Z) : Prop :=
    0 <= word.unsigned w < 2 ^ n.

  Record enum {elts : list word} {size : Z} :=
    { enum_size_ok :
        Forall (fun w => has_size w size) elts;
      enum_unique : unique_words elts;
      enum_member (w : word) := In w elts;
    }.
  Global Arguments enum : clear implicits.

  Definition boolean (w : word) : Prop := (w = word.of_Z 0 \/ w = word.of_Z 1).
End WithWord.

(* changes H : unique_words [a;b;c] into a <> b, a <> c, b <> c *)
Ltac simplify_unique_words_in H :=
  lazymatch type of H with
  | unique_words ?words =>
    let H' := fresh in
    cbv [unique_words] in H;
    pose proof (List.NoDup_dedup word.eqb words) as H';
    rewrite H in H'; clear H;
    repeat lazymatch goal with
           | H : List.NoDup [] |- _ => clear H
           | H : List.NoDup (_ :: _) |- _ => inversion H; clear H; subst; cbv [List.In] in *
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H
           | H : _ /\ _ |- _ => destruct H
           end
  | ?t => fail "expected hypothesis of type [unique_words _], got one of type" t
  end.
