(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

From Coq Require Import Bool ZArith NaryFunctions Vector.
From Arrow Require Import Category Arrow .
From Cava Require Import Arrow.CircuitArrow Arrow.CircuitSemantics.

Import VectorNotations.

Fixpoint no_delays {i o} (c: Circuit i o): bool :=
  match c with
  | Primitive (Delay _) => false
  | Composition _ _ _ f g => no_delays f && no_delays g
  | First _ _ _ f => no_delays f
  | Second _ _ _ f => no_delays f
  | Loopr _ _ _ f => no_delays f
  | Loopl _ _ _ f => no_delays f
  | _ => true
  end.

Fixpoint no_loops {i o} (c: Circuit i o): bool :=
  match c with
  | Composition _ _ _ f g => no_loops f && no_loops g
  | First _ _ _ f => no_loops f
  | Second _ _ _ f => no_loops f
  | Loopr _ _ _ f => false
  | Loopl _ _ _ f => false
  | _ => true
  end.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Definition is_combinational {i o: Kind} (c: i ~> o) :=
  no_loops c && no_delays c = true.

Ltac simply_combinational :=
  vm_compute; reflexivity.
  (* repeat match goal with
  | [ H |- True ] => exact I
  no_loops c && no_delays c.
  end. *)
  (* apply mkCombinational;
  lazy;
  repeat lazymatch goal with
  | [ |- True ] => exact I
  | [ |- forall p, (?H1 -> ?H2 -> p) -> p ] =>
    let x := fresh in (let y := fresh in (
      intros x y; apply y; clear x y
    ))
  | [ |- _ ] => fail "Term wasn't simply combinational"
  end. *)

Lemma is_combinational_first: forall x y z (circuit: x ~> y),
  is_combinational (first circuit : x**z ~> y**z) =
  is_combinational circuit.
Proof. tauto. Qed.

Lemma is_combinational_second: forall x y z (circuit: x ~> y),
  is_combinational (second circuit : z**x ~> z**y) =
  is_combinational circuit.
Proof. tauto. Qed.

Section example.
  Definition ex_loopr {x y z: Kind} (c: x**z ~> y**z): x ~> y
    := loopr c.
  Definition ex_loopl {x y z: Kind} (c: z**x ~> z**y): x ~> y
    := loopl c.

  Example loopl_is_not_combinational : forall (x y z: Kind) (c: z**x ~> z**y),
    ~ is_combinational (ex_loopl c).
  Proof. vm_compute. intros. inversion x3. Qed.

  Example loopr_is_not_combinational : forall (x y z: Kind) (c: x**z ~> y**z),
    ~ is_combinational (ex_loopr c).
  Proof. vm_compute. intros. inversion x3. Qed.

  Example not_gate_is_combinational :
    is_combinational (Primitive Not).
  Proof.  simply_combinational. Qed.
End example.

Definition proj_i {i o} (c: Circuit i o) := i.
Definition proj_o {i o} (c: Circuit i o) := o.

Fixpoint denote_destruct {i o} (c: Circuit i o) {struct c}:
  denote_kind (proj_i c) * denote_kind (proj_o c) -> Prop
  :=
  match c as c' return (denote_kind (proj_i c') * denote_kind (proj_o c')) -> Prop with
  | Composition X Y Z f g =>
      fun '(x,z) => exists y, denote_destruct f (x, y) -> denote_destruct g (y, z)
  | First _ _ _ f =>
      fun '((x,y),(z,w)) =>
      y = w -> denote_destruct f (x, z)
  | Second _ _ _ f =>
      fun '((x,y),(z,w)) =>
      x = z -> denote_destruct f (y, w)
  | Structural (Id _) => fun '(x,y) => x = y
  | Structural (Cancelr X) => fun '((x,y),z) => x = z
  | Structural (Cancell X) => fun '((x,y),z) => y = z
  | Structural (Uncancell _) => fun '(x,(y,z)) => x = z
  | Structural (Uncancelr _) => fun '(x,(y,z)) => x = y
  | Structural (Assoc _ _ _) => fun '(((x,y),z), (a,(b,c))) => x = a /\ y = b /\ z = c
  | Structural (Unassoc _ _ _) => fun '((x,(y,z)), ((a,b),c)) => x = a /\ y = b /\ z = c
  | Structural (Drop x) => fun _ => True
  | Structural (Swap x y) => fun '((x,y),(a,b)) => x=b /\ y=a
  | Structural (Copy x) => fun '(x,(a,b)) => x=a/\x=b
  | f => fun '(i,o) => combinational_evaluation' f i = o
  end.
