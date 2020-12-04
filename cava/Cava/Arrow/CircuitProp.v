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

Require Import Coq.Bool.Bool Coq.ZArith.ZArith Coq.Numbers.NaryFunctions Coq.Vectors.Vector.
Require Import Cava.Arrow.Classes.Category.
Require Import Cava.Arrow.Classes.Arrow.
Require Import Cava.Arrow.CircuitArrow Cava.Arrow.CircuitSemantics.
Require Import Cava.Arrow.ArrowKind Cava.Arrow.Primitives.

Import VectorNotations.
Import CategoryNotations.

Fixpoint no_delays {i o} (c: Circuit i o): bool :=
  match c with
  | Delay _ => false
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

Fixpoint min_buffering {i o} (n: nat) (c: Circuit i o): nat :=
  match c with
  | Delay _ => S n
  | Composition _ _ _ f g => min (min_buffering n f) (min_buffering n g)
  | First _ _ _ f => min_buffering n f
  | Second _ _ _ f => min_buffering n f
  | Loopr _ _ _ f => min_buffering n f
  | Loopl _ _ _ f => min_buffering n f
  | _ => n
  end.

Fixpoint valid_loops {i o} (c: Circuit i o): bool :=
  match c with
  | Composition _ _ _ f g => valid_loops f && valid_loops g
  | First _ _ _ f => valid_loops f
  | Second _ _ _ f => valid_loops f
  | Loopr _ _ _ f => (0 <? min_buffering 0 f) && valid_loops f
  | Loopl _ _ _ f => (0 <? min_buffering 0 f) && valid_loops f
  | _ => true
  end.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Definition is_combinational {i o: Kind} (c: i ~> o) :=
  no_loops c && no_delays c = true.

Ltac simply_combinational :=
  vm_compute; reflexivity.

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
    is_combinational (Primitive (P1 Not)).
  Proof.  simply_combinational. Qed.
End example.

