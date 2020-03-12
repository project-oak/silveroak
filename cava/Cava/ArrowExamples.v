Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.

Require Import Cava.Arrow.
Require Import Cava.Netlist.

Section Example1.


  (* Implement a NAND circuit by composing an AND gate and INV gate. *)
  Definition nand
    {Cava: Cava}
    := and_gate >>> not_gate.

  (* An implementation of an XOR gate made out of the NAND circuit
     defined above. *)
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
  Proof. 
    intros.
    destruct a.
    unfold uncurry.
    unfold nandb.
    unfold nand.
    simpl.
    f_equal.
  Qed.

  Lemma xor_is_xorb: forall a:(bool*bool), (@xor CoqCava) a = (uncurry xorb) a.
  Proof.
    intros.
    unfold xor.
    unfold nand.
    unfold uncurry.
    simpl.
    destruct a.
    simpl.
    btauto.
  Qed.

  Definition xorArrowNetlist := arrowToHDLModule
    "xorArrow"
    (@xor NetlistCava)
    (fun '(l,r) =>
      [ mkPort "input1" (BitPort l)
      ; mkPort "input2" (BitPort r)
      ])
    (fun o => [mkPort "output1" (BitPort o)]).
  (* Compute the circuit netlist for the XOR made up of NANDs made up of ANDs and INVs *)
  Eval compute in xorArrowNetlist.
  (* For extraction *)
  Definition xorArrow := 
    let '(nl, count) := xorArrowNetlist
    in mkCavaState count [] false nl.

End Example1.

Section Example2.
  (*nand previous output and current input, output delayed 1 cycle*)
  Definition loopedNand
    {Cava: CavaDelay}
    {ArrowLoop: @ArrowLoop (@cava_delay_arr Cava)}
    : bit ~> bit :=
    loopl (nand >>> delay_gate >>> copy).

  Definition loopedNandArrowNetlist := arrowToHDLModule
    "loopedNandArrow"
    (@loopedNand NetlistCavaDelay NetlistLoop)
    (fun i => [ mkPort "input1" (BitPort i)])
    (fun o => [mkPort "output1" (BitPort o)]).
  Eval compute in loopedNandArrowNetlist.
  Definition loopedNandArrow := 
    let '(nl, count) := loopedNandArrowNetlist
    in mkCavaState count [] true nl.
End Example2.
