(* names for the MMIO load/store events to record in the I/O trace *)

Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Numbers.DecimalNat.

Definition READ_PREFIX := "MMIOREAD".
Definition READ8 := READ_PREFIX ++ "8".
Definition READ16 := READ_PREFIX ++ "16".
Definition READ32 := READ_PREFIX ++ "32".
Definition READ64 := READ_PREFIX ++ "64".

Definition WRITE_PREFIX := "MMIOWRITE".
Definition WRITE8 := WRITE_PREFIX ++ "8".
Definition WRITE16 := WRITE_PREFIX ++ "16".
Definition WRITE32 := WRITE_PREFIX ++ "32".
Definition WRITE64 := WRITE_PREFIX ++ "64".

Definition natToStr(n: nat): string := DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Definition access_size_to_MMIO_read(sz: nat): string :=
  READ_PREFIX ++ natToStr (sz * 8).

Definition access_size_to_MMIO_write(sz: nat): string :=
  WRITE_PREFIX ++ natToStr (sz * 8).

Lemma string_of_uint_inj: forall n m, NilEmpty.string_of_uint n = NilEmpty.string_of_uint m -> n = m.
Proof.
  intros. apply (f_equal NilEmpty.uint_of_string) in H.
  do 2 rewrite NilEmpty.usu in H.
  inversion H.
  reflexivity.
Qed.

Lemma natToStr_inj: forall n m, natToStr n = natToStr m -> n = m.
Proof.
  unfold natToStr. intros.
  apply string_of_uint_inj in H.
  apply Unsigned.to_uint_inj in H.
  exact H.
Qed.

Lemma access_size_to_MMIO_read_inj: forall sz1 sz2,
    access_size_to_MMIO_read sz1 = access_size_to_MMIO_read sz2 ->
    sz1 = sz2.
Proof.
  unfold access_size_to_MMIO_read.
  intros. inversion H.
  apply natToStr_inj in H1.
  eapply PeanoNat.Nat.mul_cancel_r. 2: eassumption.
  discriminate.
Qed.
