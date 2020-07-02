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

From Arrow Require Import Category ClosureConversion.
From Cava Require Import Arrow.ArrowExport.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Coq Require Import Lists.List.
Import ListNotations.

Section notation.
  Import KappaNotation. 

  Variable var: Kind -> Kind -> Type.

  Definition xilinxFullAdder
    : CavaExpr var << Bit, << Bit, Bit >>, Unit >> << Bit, Bit >> :=
    <[ \ cin ab =>
      let '(a,b) = ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.
End notation.

Open Scope kind_scope.
Definition xilinxFullAdder_arrow {cava: Cava}
  : << Bit, << Bit, Bit >> >> ~> <<Bit, Bit>>
  := to_arrow @xilinxFullAdder.

Lemma xilinxFullAdder_is_combinational: wf_combinational xilinxFullAdder_arrow.
Proof. combinational_obvious. Qed.
