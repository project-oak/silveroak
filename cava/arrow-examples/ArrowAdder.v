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
Require Import Cava.Arrow.Instances.Netlist.

Require Import Cava.Types.
Require Import Cava.Netlist.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Coq Require Import Lists.List.
Import ListNotations.


Definition halfAdder'
: Kappa (bit ** bit ** unit) (bit ** bit) :=
<[ \ a b =>
   let part_sum = !xor_gate a b in
   let carry = !and_gate a b in
(part_sum, carry)
]>.

Definition fullAdder'
: Kappa (bit ** ((bit ** bit) ** unit)) (bit ** bit) :=
<[ \ cin ab =>
  let a = fst' ab in
  let b = snd' ab in
  let abl_abh = ~!(halfAdder') a b in
  let abl = fst' abl_abh in
  let abh = snd' abl_abh in
  let abcl_abch = ~!(halfAdder') abl cin in
  let abcl = fst' abcl_abch in
  let abch = snd' abcl_abch in
  let cout = !xor_gate abh abch in
  (abcl, cout)
]>.

Definition fullAdder_netlist := arrowToHDLModule
  "fullAdder"
  (toCava NetlistCava (Closure_conversion fullAdder'))
  ("cin", (("a", "b"), tt))
  ("sum", "cout").

Definition fullAdderInterface
  := mkCircuitInterface "fullAdder"
     (Tuple2 (One ("cin", Bit)) (Tuple2 (One ("a", Bit)) (One ("b", Bit))))
     (Tuple2 (One ("sum", Bit)) (One ("cout", Bit)))
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

Definition fullAdder `{Cava}: (bit ** (bit ** bit) ** unit) ~> bit ** bit
   := toCava _ (Closure_conversion fullAdder').

Definition fullAdder_tb_expected_outputs
   := map (fun '(cin, (a,b)) => (@fullAdder Combinational) (cin, ((a, b), tt)))
      fullAdder_tb_inputs.

Definition fullAdder_tb :=
  testBench "fullAdder_tb" fullAdderInterface
            fullAdder_tb_inputs fullAdder_tb_expected_outputs.