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

Section instance.

Instance ConjPropKindCategory : Category Kind := {
  morphism X Y := Prop;
  compose _ _ _ f g := f /\ g;
  id X := True;
}.

Instance ConjPropKindArrow : Arrow _ ConjPropKindCategory Unit Tuple := {
  first _ _ _ p := p;
  second _ _ _ p := p;

  cancelr X := True;
  cancell X := True;

  uncancell _ := True;
  uncancelr _ := True;

  assoc _ _ _ := True;
  unassoc _ _ _ := True;
}.

Instance TrueDrop : ArrowDrop ConjPropKindArrow := { drop _ := True }.
Instance TrueCopy : ArrowCopy ConjPropKindArrow := { copy _ := True }.
Instance TrueSwap : ArrowSwap ConjPropKindArrow := { swap _ _ := True }.

Instance TrueSTKC : ArrowSTKC ConjPropKindArrow := { }.

Instance SubLoop : ArrowLoop ConjPropKindArrow := { loopl _ _ _ l := l; loopr _ _ _ l := l }.
Instance FalseLoop : ArrowLoop ConjPropKindArrow := { loopl _ _ _ _ := False; loopr _ _ _ _ := False }.

Instance NoDelays : Cava := {
  cava_arrow := ConjPropKindArrow;
  cava_arrow_stkc := TrueSTKC;
  cava_arrow_loop := SubLoop;

  constant b := True;
  constant_bitvec n v := True;
  mk_module _ _ _name f := f;
  not_gate := True;
  and_gate := True;
  nand_gate := True;
  or_gate := True;
  nor_gate := True;
  xor_gate := True;
  xnor_gate := True;
  buf_gate := True;
  xorcy := True;
  muxcy := True;
  unsigned_add _ _ _ := True;
  lut _ _ := True;

  empty_vec o := True;
  index n o := True;
  cons n o := True;
  snoc n o:= True;
  uncons n o:= True;
  unsnoc n o:= True;
  concat n m o := True;
  split n m o _ := True;
  slice n x y o _ _ := True;

  delay_gate _ := False;
}.

Instance NoLoops : Cava := {
  cava_arrow := ConjPropKindArrow;
  cava_arrow_stkc := TrueSTKC;
  cava_arrow_loop := FalseLoop;

  constant b := True;
  constant_bitvec n v := True;
  mk_module _ _ _name f := f;
  not_gate := True;
  and_gate := True;
  nand_gate := True;
  or_gate := True;
  nor_gate := True;
  xor_gate := True;
  xnor_gate := True;
  buf_gate := True;
  xorcy := True;
  muxcy := True;
  unsigned_add _ _ _ := True;
  lut _ _ := True;

  empty_vec o := True;
  index n o := True;
  cons n o := True;
  snoc n o:= True;
  uncons n o:= True;
  unsnoc n o:= True;
  concat n m o := True;
  split n m o _ := True;
  slice n x y o _ _ := True;

  delay_gate _ := True;
}.

End instance.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Definition is_combinational {i o: Kind} (c: forall (cava: Cava), i ~[cava]~> o) := 
  c NoLoops /\ c NoDelays.

Definition mkCombinational {i o: Kind} (c: forall (cava: Cava), i ~[cava]~> o)
  : c NoLoops -> c NoDelays -> is_combinational c.
Proof.
  intros.
  unfold is_combinational.
  tauto.
Qed.

Lemma is_combinational_first: forall x y z (circuit: forall (cava: Cava), x ~> y),
  is_combinational (fun cava => first (circuit cava) : x**z ~[cava]~> y**z) =   
  is_combinational circuit.
Proof.
  intros.
  tauto.
Qed.

Lemma is_combinational_second: forall x y z (circuit: forall (cava: Cava), x ~> y),
  is_combinational (fun cava => second (circuit cava) : z**x ~[cava]~> z**y) =   
  is_combinational circuit.
Proof.
  intros.
  tauto.
Qed.

Lemma modular_prop: forall (x y z : Kind)
  (A: Arrow Kind ConjPropKindCategory Unit Tuple)
  (f: x ~[A]~> y) (g: y ~[A]~> z),
  (f >>> g) = 
  (g /\ f).
Proof.
  intros.
  tauto.
Qed.

Lemma decompose_combinational: forall x y z
  (f: forall (cava: Cava), x ~> y)
  (g: forall (cava: Cava), y ~> z),
  is_combinational (fun cava => (f cava) >>> (g cava) : x ~[cava]~> z ) -> 
  is_combinational g /\ is_combinational f.
Proof.
  intros.
  unfold is_combinational in *.
  cbn in H.
  tauto.
Qed.

Section example.
  Definition ex_loopr {x y z: Kind} (cava: Cava) (c: x**z ~[cava]~> y**z): x ~[cava]~> y
    := loopr c.
  Definition ex_loopl {x y z: Kind} (cava: Cava) (c: z**x ~[cava]~> z**y): x ~[cava]~> y
    := loopl c.

  Lemma loopl_is_not_combinational : forall (x y z: Kind) (c: forall (cava: Cava), z**x ~[cava]~> z**y),
    ~ is_combinational (fun cava => ex_loopl cava (c cava)).
  Proof.
    intros.
    unfold is_combinational.
    tauto.
  Qed.

  Lemma loopr_is_not_combinational : forall (x y z: Kind) (c: forall (cava: Cava), x**z ~[cava]~> y**z),
    ~ is_combinational (fun cava => ex_loopr cava (c cava)).
  Proof.
    intros.
    unfold is_combinational.
    tauto.
  Qed.
End example.