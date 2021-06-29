(* names for the MMIO load/store events to record in the I/O trace *)

Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import bedrock2.Syntax.

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

Require Import coqutil.Word.Interface.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.ZArith.ZArith.

Definition ZToStr(n: Z): string := DecimalString.NilZero.string_of_int (Z.to_int n).

Definition access_size_to_MMIO_suffix(width: Z)(sz: access_size): string :=
  match sz with
  | access_size.one => "8"
  | access_size.two => "16"
  | access_size.four => "32"
  | access_size.word => ZToStr width
  end.

(* We pass an unnecessary `word` instance to the following definitions just to make
   `width` inferrable, later we might make a typeclass for just `width` and then we
   can remove the `word`. *)
#[export] Hint Mode word.word - : typeclass_instances.

Definition access_size_to_MMIO_read{width}{word: word.word width}(sz: access_size): string :=
  READ_PREFIX ++ access_size_to_MMIO_suffix width sz.

Definition access_size_to_MMIO_write{width}{word: word.word width}(sz: access_size): string :=
  WRITE_PREFIX ++ access_size_to_MMIO_suffix width sz.

Lemma access_size_to_MMIO_read_inj{width}{word: word.word width}: forall sz1 sz2,
    access_size_to_MMIO_read sz1 = access_size_to_MMIO_read sz2 ->
    sz1 = sz2.
Proof.
  destruct sz1; destruct sz2; cbn; try congruence; intros.
  3: {
    inversion H.
    (* doesn't hold!! *)
Admitted.
