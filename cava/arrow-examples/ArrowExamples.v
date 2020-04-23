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

Require Import Nand.
Require Import Xor.
Require Import FeedbackNand.

Local Open Scope string_scope.

Definition twoBits
  `{Cava}
  : unit ~> (bit**bit) :=
  copy
  >>> first (constant true)
  >>> second (constant false).

Definition twoBools
  `{Cava}
  (x y: bool): unit ~> (bit**bit) :=
  copy
  >>> first (constant x)
  >>> second (constant y).

Definition nandb : bool -> bool -> bool := fun a b => negb (a && b).
Definition uncurry {a b c} (f: a -> b -> c) : (a*b) -> c := fun xy => f (fst xy) (snd xy).

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

  Definition nandArrow := arrowToHDLModule
    "nandArrow"
    (@nand NetlistCava)
    ("input1","input2")
    ("output1").
  Eval compute in nandArrow.

  Definition xorArrow := arrowToHDLModule

    "xorArrow"
    (@xor NetlistCava)
    ("input1","input2")
    ("output1").
  (* Compute the circuit netlist for the XOR made up of NANDs made up of ANDs and INVs *)
  Eval compute in xorArrow.

  Definition feedbackNandArrow := arrowToHDLModule
    "feedbackNandArrow"
    (@feedbackNand NetlistCavaDelay NetlistLoop)
    ("input1")
    ("output1").
  Eval compute in feedbackNandArrow.
End NetlistExamples.
