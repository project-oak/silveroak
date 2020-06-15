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

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Instances.Combinational.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Coq Require Import Lists.List.
Import ListNotations.

Section definition.
  Import KappaNotation.

  Variable var: Kind -> Kind -> Type.

  Definition halfAdder
  : kappa_sugared var << Bit, Bit, Unit >> <<Bit, Bit>> :=
  <[ \ a b =>
    let part_sum = xor a b in
    let carry = and a b in
    (part_sum, carry)
  ]>.

  Definition fullAdder
  : kappa_sugared var << Bit, << Bit, Bit >>, Unit >> <<Bit, Bit>> :=
  <[ \ cin ab =>
    let '(a,b) = ab in
    let '(abl, abh) = !halfAdder a b in
    let '(abcl, abch) = !halfAdder abl cin in
    let cout = xor abh abch in
    (abcl, cout)
  ]>.

End definition.

Definition fullAdder_structure := to_constructive (Desugar fullAdder) (ltac:(auto_kappa_wf)).

Lemma fullAdder_is_combinational: wf_combinational (toCava fullAdder_structure _).
Proof. combinational_obvious. Qed.

Require Import Cava.Arrow.Instances.Netlist.
Require Import Cava.Types.
Require Import Cava.Netlist.

Definition fullAdderInterface
  := combinationalInterface "fullAdder"
     (mkPort "cin" Bit, (mkPort "a" Bit, mkPort "b" Bit))
     (mkPort "sum" Bit, mkPort "cout" Bit)
     [].

Definition fullAdder_tb_inputs :=
  [(false, (false, false));
   (false, (true, false));
   (false, (false, true));
   (false, (true, true));
   (true, (false, false));
   (true, (true, false));
   (true, (false, true));
   (true, (true, true))
].

Definition fullAdder_netlist :=
  makeNetlist fullAdderInterface
    (toCava fullAdder_structure NetlistCava).

(* Using `evaluate_to_terms` for a nicer extracted value *)
Definition fullAdder_tb_expected_outputs  : list (bool * bool).
Proof. evaluate_to_terms fullAdder_structure fullAdder_is_combinational fullAdder_tb_inputs. Defined.

Definition fullAdder_tb :=
  testBench "fullAdder_tb" fullAdderInterface
            fullAdder_tb_inputs fullAdder_tb_expected_outputs.
