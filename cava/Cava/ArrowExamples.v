Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import btauto.Btauto.

Require Import Cava.Arrow.

Set Implicit Arguments.
Set Strict Implicit.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Example1.
  Definition nand
    {Cava: Cava}
    := and_gate >>> not_gate.

  Definition xor
    {_: Cava}
    : (bit**bit) ~> bit :=
    copy
    >>> first (nand >>> copy)                    (* ((nand,nand),(x,y)) *)
    >>> assoc                                    (* (nand,(nand,(x,y))) *)
    >>> second (unassoc >>> first nand >>> swap) (* (nand,(y, x_nand)) *)
    >>> unassoc >>> first nand                   (* (y_nand,x_nand) *)
    >>> nand.

  Definition twoBits
    {Cava: Cava}
    : unit ~> (bit**bit) :=
    copy
    >>> first (fromBool true)
    >>> second (fromBool false).

  Existing Instance CoqArr.
  Existing Instance CoqCava.

  Print xor.
  Eval simpl in (twoBits >>> and_gate) tt.
  Eval cbv in (twoBits >>> and_gate) tt.
  Eval simpl in (twoBits >>> nand) tt.
  Eval cbv in (twoBits >>> nand) tt.
  Eval simpl in (twoBits >>> xor) tt.
  Eval cbv in (twoBits >>> xor) tt.

  Definition twoBools
    {Cava: Cava}
    (x y: bool): unit ~> (bit**bit) :=
    copy
    >>> first (fromBool x)
    >>> second (fromBool y).

  Definition nandb : bool -> bool -> bool := fun a b => negb (a && b).
  Definition uncurry {a b c} (f: a -> b -> c) : (a*b) -> c := fun xy => f (fst xy) (snd xy).

  (*proofs for CoqCava e.g. direct function eval, no lists*)
  Lemma nand_is_nandb: forall a:(bool*bool), (@nand CoqCava) a = (uncurry nandb) a.
  Proof. auto. Qed.

  Lemma xor_is_xorb: forall a:(bool*bool), (@xor CoqCava) a = (uncurry xorb) a.
  Proof. 
    intros.
    unfold xor. 
    unfold nand.
    unfold uncurry.
    simpl.
    btauto.
  Qed.
End Example1.

Section Example2.
  (*nand previous output and current input, output delayed 1 cycle*)
  Definition loopedNand
    {Cava: Cava}
    {ArrowLoop: @ArrowLoop (@cava_arrow Cava)}
    `{@CavaDelay Cava}
    : bit ~> bit :=
    loopl (nand >>> delay_gate >>> copy).
End Example2.