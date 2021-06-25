(* names for the MMIO load/store events to record in the I/O trace *)

Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import bedrock2.Syntax.

Definition READ_PREFIX := "READ".
Definition READ8 := READ_PREFIX ++ "8".
Definition READ16 := READ_PREFIX ++ "16".
Definition READ32 := READ_PREFIX ++ "32".
Definition READW := READ_PREFIX ++ "W". (* read 32 or 64 bits depending on bitwidth of machine *)

Definition WRITE_PREFIX := "WRITE".
Definition WRITE8 := WRITE_PREFIX ++ "8".
Definition WRITE16 := WRITE_PREFIX ++ "16".
Definition WRITE32 := WRITE_PREFIX ++ "32".
Definition WRITEW := WRITE_PREFIX ++ "W". (* write 32 or 64 bits depending on bitwidth of machine *)

Definition access_size_to_MMIO_suffix(sz: access_size): string :=
  match sz with
  | access_size.one => "8"
  | access_size.two => "16"
  | access_size.four => "32"
  | access_size.word => "W"
  end.

Definition access_size_to_MMIO_read(sz: access_size): string :=
  READ_PREFIX ++ access_size_to_MMIO_suffix sz.

Definition access_size_to_MMIO_write(sz: access_size): string :=
  WRITE_PREFIX ++ access_size_to_MMIO_suffix sz.

Lemma access_size_to_MMIO_read_inj: forall sz1 sz2,
    access_size_to_MMIO_read sz1 = access_size_to_MMIO_read sz2 ->
    sz1 = sz2.
Proof.
  destruct sz1; destruct sz2; cbv; congruence.
Qed.

Lemma access_size_to_MMIO_write_inj: forall sz1 sz2,
    access_size_to_MMIO_write sz1 = access_size_to_MMIO_write sz2 ->
    sz1 = sz2.
Proof.
  destruct sz1; destruct sz2; cbv; congruence.
Qed.
