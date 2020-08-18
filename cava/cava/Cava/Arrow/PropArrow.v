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

From Coq Require Import Bool ZArith NaryFunctions VectorDef.
From Arrow Require Import Category Arrow Kappa ClosureConversion.
From Cava Require Import Arrow.CavaArrow.

Import VectorNotations.

Fixpoint no_delays {i o} (c: Circuit i o): bool :=
  match c with
  | Primitive (delay_gate _) => false
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
    is_combinational (Primitive not_gate).
  Proof.  simply_combinational. Qed.
End example.