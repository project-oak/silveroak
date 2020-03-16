Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.Streams.

From Coq Require Import btauto.Btauto.

Require Import Cava.Arrow.
Require Import Cava.ArrowExamples.

Set Implicit Arguments.

Section CoqStreamEval.
  Instance CoqStreamCat : Category := {
    morphism X Y := Stream X -> Stream Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqStreamArr : Arrow := {
    unit := Datatypes.unit : Type;

    fork _ _ _ f g := fun xs => zipWith pair (f xs) (g xs);
    exl X Y := map fst;
    exr X Y := map snd;

    drop _ := map (fun _ => tt);
    copy _ := map (fun x => pair x x);

    swap _ _ := map (fun x => (snd x, fst x));

    uncancell _ := map (fun x => (tt, x));
    uncancelr _ := map (fun x => (x, tt));

    assoc _ _ _   := map (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)));
    unassoc _ _ _ := map (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)));
  }.

  CoFixpoint liftBool (b: bool) : Stream bool
  := Cons b (liftBool b).

  Instance CoqStreamCava : Cava := {
    bit := bool;

    fromBool b := fun _ => liftBool b;

    not_gate := map (fun b => negb b);
    and_gate := map (fun xy => andb (fst xy) (snd xy));
  }.
End CoqStreamEval.

Section StreamProofs.
  (* 1. explicit proof - manual method *)
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

  (* chaining inbult tactics - automatic *)
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
