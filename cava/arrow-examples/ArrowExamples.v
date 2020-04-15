Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.Streams.

Import ListNotations.

From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.

Require Import Cava.Netlist.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Coq.
Require Import Cava.Arrow.Instances.Netlist.
Require Import Cava.Arrow.Instances.Stream.

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
  >>> first (constant true)
  >>> second (constant false).

Definition twoBools
  {Cava: Cava}
  (x y: bool): unit ~> (bit**bit) :=
  copy
  >>> first (constant x)
  >>> second (constant y).

Definition nandb : bool -> bool -> bool := fun a b => negb (a && b).
Definition uncurry {a b c} (f: a -> b -> c) : (a*b) -> c := fun xy => f (fst xy) (snd xy).

(*nand previous output and current input, output delayed 1 cycle*)
Definition loopedNand
  {Cava: CavaDelay}
  {ArrowLoop: @ArrowLoop (@cava_delay_arr Cava)}
  : bit ~> bit :=
  loopl (nand >>> delay_gate >>> copy).

Existing Instance CoqArr.
Existing Instance CoqCava.

Print xor.
Eval simpl in (twoBits >>> and_gate) tt.
Eval cbv in (twoBits >>> and_gate) tt.
Eval simpl in (twoBits >>> nand) tt.
Eval cbv in (twoBits >>> nand) tt.
Eval simpl in (twoBits >>> xor) tt.
Eval cbv in (twoBits >>> xor) tt.

Section SimpleExamples.
  (* Destructure context as much as possible then try to solve.
  This works for CoqCava with simple boolean circuits as the cases
  generated from destructuring tuples of booleans fully are quite simple.
  *)
  Ltac simple_boolean_circuit :=
    intros;
      repeat match goal with
        | [ H: _ |- _ ] => destruct H
      end;
    auto.

  (*proofs for CoqCava e.g. direct function eval, no lists*)
  Lemma nand_is_nandb: forall a:(bool*bool), (@nand CoqCava) a = (uncurry nandb) a.
  Proof. simple_boolean_circuit. Qed.

  Lemma xor_is_xorb: forall a:(bool*bool), (@xor CoqCava) a = (uncurry xorb) a.
  Proof. simple_boolean_circuit. Qed.

End SimpleExamples.

Section StreamProofs.
  (* TODO: revive this proof? didn't survive refactor *)
  (*(* 1. explicit proof - manual method *)
  Lemma nand_is_combinational_1:
    forall a:Stream (bool*bool),
    EqSt ((@nand CoqStreamCava) a) (map (uncurry nandb) a).
  Proof.
    cofix proof. (* make a coinduction hypothesis called "proof" *)
    intros.
    constructor. (* case analysis 1 & 2*)
    - constructor. (* 1) _don't_ use proof for head *)
    - apply proof. (* 2) use proof on tail *)
    (*using proof on both 1 & 2 would causes a recursive proof definition
    which would fail when trying to QED *)
  Qed.
  *)

  (* TODO: revive this proof? didn't survive refactor *)
  (*(* chaining inbult tactics - automatic *)
  Lemma nand_is_combinational_2:
    forall a:Stream (bool*bool),
    EqSt ((@nand CoqStreamCava) a) (map (uncurry nandb) a).
  Proof.
    cofix proof; intros; constructor;
      [ clear proof | try (apply proof; clear proof) ].
    auto.
    (* in the commented method, the square brackets causes
      - clear proof; auto
      - apply proof; clear proof; auto. *)
  Qed.
  *)

  Ltac simple_boolean_stream_circuit cofix_proof stream :=
    cofix cofix_proof;
    intro stream;
    destruct stream;
    constructor;
      [ clear cofix_proof; revert stream;
        repeat match goal with
          | H: _ |- _ => destruct H
        end
      | try (apply cofix_proof; clear cofix_proof ) ];
      auto.

  (* 3. using custom built tactic - automatic *)
  Lemma nand_is_combinational_3:
    forall a:Stream (bool*bool),
    EqSt ((@nand CoqStreamCava) a) (map (uncurry nandb) a).
  Proof.
    simple_boolean_stream_circuit proof stream.
  Qed.

  Lemma xor_is_combinational:
    forall a:Stream (bool*bool),
    EqSt ((@xor CoqStreamCava) a) (map (uncurry xorb) a).
  Proof.
    simple_boolean_stream_circuit proofs stream.
  Qed.

End StreamProofs.

Section NetlistExamples.
  Definition xorArrowNetlist := arrowToHDLModule
    "xorArrow"
    (@xor NetlistCava)
    (fun '(l,r) =>
      [ mkPort "input1" (One Bit) l
      ; mkPort "input2" (One Bit) r
      ])
    (fun o => [mkPort "output1" (One Bit) o]).
  (* Compute the circuit netlist for the XOR made up of NANDs made up of ANDs and INVs *)
  Eval compute in xorArrowNetlist.
  (* For extraction *)
  Definition xorArrow :=
    let '(nl, count) := xorArrowNetlist
    in mkCavaState count false nl.

  Definition loopedNandArrowNetlist := arrowToHDLModule
    "loopedNandArrow"
    (@loopedNand NetlistCavaDelay NetlistLoop)
    (fun i => [ mkPort "input1" (One Bit) i])
    (fun o => [mkPort "output1" (One Bit) o]).
  Eval compute in loopedNandArrowNetlist.
  Definition loopedNandArrow :=
    let '(nl, count) := loopedNandArrowNetlist
    in mkCavaState count true nl.
End NetlistExamples.
