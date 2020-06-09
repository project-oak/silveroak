Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.Streams.

Import ListNotations.

From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.

Require Import Cava.Netlist.
Require Import Cava.Types.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Combinational.
Require Import Cava.Arrow.Instances.Netlist.

Require Import ArrowExamples.Concatenative.Nand.
Require Import ArrowExamples.Concatenative.Xor.
Require Import ArrowExamples.Concatenative.FeedbackNand.

Local Open Scope string_scope.

Definition nandb : bool -> bool -> bool := fun a b => negb (a && b).
Definition uncurry {a b c} (f: a -> b -> c) : (a*b) -> c := fun xy => f (fst xy) (snd xy).

Existing Instance CoqArr.
Existing Instance Combinational.

Print xor.

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
  Lemma nand_is_nandb: forall a:(bool*bool), (@nand Combinational) a = (uncurry nandb) a.
  Proof. simple_boolean_circuit. Qed.

  Lemma xor_is_xorb: forall a:(bool*bool), (@xor Combinational) a = (uncurry xorb) a.
  Proof. simple_boolean_circuit. Qed.

End SimpleExamples.

Section NetlistExamples.
  (* Test bench tables for generated SystemVerilog simulation test bench *)
  Definition arrow_nand_tb_inputs : list (bool * bool) :=
  [(false, false); (false, true); (true, false); (true, true)].

  (* Compute expected outputs. *)
  Definition arrow_nand_tb_expected_outputs : list bool :=
  List.map (@nand Combinational) arrow_nand_tb_inputs.

  Definition nand2Interface
    := combinationalInterface "nandArrow"
       (mkPort "input1" Bit, mkPort "input2" Bit)
       (mkPort "output1" Bit)
       [].

  Definition nandArrow :=
    makeNetlist nand2Interface
      (removeRightmostUnit (@nand NetlistCava)).

  Definition arrow_nand2_tb :=
  testBench "nandArrow_tb" nand2Interface
            arrow_nand_tb_inputs arrow_nand_tb_expected_outputs.


  (* Test bench tables for generated SystemVerilog simulation test bench *)
  Definition arrow_xor_tb_inputs : list (bool * bool) :=
  [(false, false); (false, true); (true, false); (true, true)].

  (* Compute expected outputs for xorArrow. *)
  Definition arrow_xor_tb_expected_outputs : list bool :=
  List.map (@xor Combinational) arrow_xor_tb_inputs.

  Definition xorInterface
    := combinationalInterface "xorArrow"
       (mkPort "input1" Bit, mkPort "input2" Bit)
       (mkPort "output1" Bit)
       [].

  Definition xorArrow :=
    makeNetlist xorInterface
      (removeRightmostUnit (@xor NetlistCava)).

  Definition arrow_xor_tb :=
  testBench "xorArrow_tb" xorInterface
            arrow_xor_tb_inputs arrow_xor_tb_expected_outputs.

  Definition feedbackNandArrow_tb_inputs :=
  [false; (* 10 *)
   false; (* 20 *)
   true;  (* 30 *)
   true;  (* 40 *)
   true;  (* 50 *)
   true;  (* 60 *)
   false; (* 70 *)
   false; (* 80 *)
   true;  (* 90 *)
   true;  (* 100 *)
   true;  (* 110 *)
   true   (* 120 *)
  ] .

  (* TODO: Replace with Cava computed results. *)
  Definition feedbackNandArrow_tb_expected_outputs :=
  [false; (* 10 *)
   true;  (* 20 *)
   true;  (* 30 *)
   false; (* 40 *)
   true;  (* 50 *)
   false; (* 60 *)
   true;  (* 70 *)
   true;  (* 80 *)
   true;  (* 90 *)
   false; (* 100 *)
   true;  (* 110 *)
   false  (* 120 *)
  ].

  Definition feedbackNandInterface
    := sequentialInterface "feedbackNandArrow"
       "clk" PositiveEdge "rst" PositiveEdge
       (mkPort "input1" Bit)
       (mkPort "output1" Bit)
       [].

  Definition feedbackNandArrow :=
    makeNetlist feedbackNandInterface
      (removeRightmostUnit (@feedbackNand NetlistCavaDelay NetlistLoop)).

  Definition feedbackNandArrow_tb :=
  testBench "feedbackNandArrow_tb" feedbackNandInterface
            feedbackNandArrow_tb_inputs feedbackNandArrow_tb_expected_outputs.

End NetlistExamples.
