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

From Coq Require Import Lists.List NArith Lia.
Import ListNotations.

Section notation.
  Import KappaNotation.
  Local Open Scope kind_scope.

  Definition halfAdder
  : << Bit, Bit, Unit >> ~> <<Bit, Bit>> :=
    (* The bracket pairing `<[` `]>` opens a circuit expression scope, 
    see readme.md for more information *) 
  <[ \ a b =>
    let part_sum = xor a b in
    let carry = and a b in
    (part_sum, carry)
  ]>.

  Definition fullAdder
  : << Bit, << Bit, Bit >>, Unit >> ~> <<Bit, Bit>> :=
  <[ \ cin ab =>
    let '(a,b) = ab in
    (* Since 'halfAdder' is in the larger Coq scope, and is not a local variable,
    they must be escaped with ! See the readme.md in this file for more explanation*)
    let '(abl, abh) = !halfAdder a b in
    let '(abcl, abch) = !halfAdder abl cin in
    let cout = xor abh abch in
    (abcl, cout)
  ]>.

  (* Combinators *)
  Definition below {A B C D E F G: Kind}
    (r: << A, B, Unit >> ~> << G, D >>)
    (s: << G, C, Unit >> ~> << F, E >>)
    : << A, <<B, C>>, Unit >> ~> << F, <<D, E>> >> :=
  <[ \ a bc =>
    let '(b, c) = bc in
    let '(g, d) = !r a b in
    let '(f, e) = !s g c in
    (f, (d, e))
  ]>.

  (* Replicate is a type created by replicating a type n times, 
  and connecting them by a right imbalanced tuple structure.

  Since the above formulation of 'below' pairs the inputs and outputs 
  as a tuple (rather requiring the types are equal and appending as a vector), 
  'replicate' allows us to refer to type arrising from multiple
  applications of 'below'. 
  *)
  Fixpoint replicate A n : Kind :=
    match n with
    | O => Unit
    | S O => A
    | S n => <<A, replicate A n>>
    end.

  Fixpoint col {A B C: Kind} n
    (circuit: << A, B, Unit >> ~> <<A, C>>)
    {struct n}: 
      << A, replicate B (S n), Unit >> ~>
      << A, replicate C (S n)>> :=
    match n with
    | O => <[ \a b => !circuit a b ]> 
    | S n' =>
      let column_above := (col n' circuit) in
      below circuit column_above 
    end.

  Lemma col_cons: forall {A B C}
    (circuit: << A, B, Unit >> ~> <<A, C>>),
    forall n, col (S n) circuit = below circuit (col n circuit).
  Proof.
    intros.
    auto.
  Qed.

  Fixpoint interleave n
    : << Vector Bit (S n), Vector Bit (S n), Unit >> ~>
      << replicate <<Bit, Bit>> (S n) >> :=
  match n with
  (* Since for n = 0 -> Vector 1 Bit, we have to index into the variables to retrieve their values.
  This is done with familiar 'x[_]' syntax, although numeric constants require prepending with '#'.
  The index can be any expression. See readme.md for more information.
  *)
  | 0 => <[\ x y => (x[#0], y[#0]) ]> 
  | S n => 
      <[\ xs ys => 
      let '(x, xs') = uncons xs in 
      let '(y, ys') = uncons ys in 
      ((x, y), (!(interleave n) xs' ys'))
    ]>
  end.

  (* As noted above, we use 'replicate' to allow us to refer to a tuple structure of a single type of kind.
  It would be convenient to interact with this variable as a vector, and so we can write a conversion
  function : *)
  Fixpoint productToVec n
    : << replicate Bit (S n), Unit >> ~>
      << Vector Bit (S n) >> :=
  match n with
  | 0 => <[\ x => x :: [] ]> 
  | S n => 
      <[\ xs => 
      let '(x, xs') = xs in 
      x :: !(productToVec n) xs'
    ]>
  end.

  Definition rippleCarryAdder' (width: nat)
    : << Bit, replicate <<Bit, Bit>> (S width), Unit >> ~>
      << Bit, replicate Bit (S width) >> :=
  <[ !(col width fullAdder) ]>.

  Definition rippleCarryAdder (width: nat)
    : << Bit, <<Vector Bit (S width), Vector Bit (S width)>>, Unit >> ~>
      << Bit, Vector Bit (S width) >> :=
  <[ \b xy =>
    let '(x,y) = xy in
    let merged = !(interleave _) x y in
    let '(carry, result) = !(rippleCarryAdder' _) b merged in
    (carry, !(productToVec _) result)
    ]>.

End notation.

Lemma fullAdder_is_combinational: is_combinational fullAdder.
Proof. simply_combinational. Qed.

Require Import Cava.Types.
Require Import Cava.Netlist.

Definition fullAdderInterface
  := combinationalInterface "fullAdder"
     (mkPort "cin" Kind.Bit, (mkPort "a" Kind.Bit, mkPort "b" Kind.Bit))
     (mkPort "sum" Kind.Bit, mkPort "cout" Kind.Bit)
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
  makeNetlist fullAdderInterface (build_netlist fullAdder).

Definition fullAdder_tb_expected_outputs  : list (bool * bool)
  := (List.map (fun i => combinational_evaluation fullAdder fullAdder_is_combinational i) fullAdder_tb_inputs) .

Definition fullAdder_tb :=
  testBench "fullAdder_tb" fullAdderInterface
            fullAdder_tb_inputs fullAdder_tb_expected_outputs.