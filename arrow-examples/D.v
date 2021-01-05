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

From Cava Require Import Arrow.ArrowExport.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Coq Require Import Lists.List NArith Lia Nat.
Import ListNotations.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
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
    : << Bit, Vector Bit (S width), Vector Bit (S width), Unit >> ~>
      << Bit, Vector Bit (S width) >> :=
  <[ \b x y =>
    let merged = !(interleave _) x y in
    let '(carry, result) = !(rippleCarryAdder' _) b merged in
    (carry, !(productToVec _) result)
    ]>.

  Definition xilinxAdder (width: nat)
    : <<Vector Bit (S width), Vector Bit (S width), Unit >> ~>
      << Vector Bit (S width) >> :=
    <[ \x y =>
      let '(carry, val) = !(rippleCarryAdder width) false' x y in val ]>.

  Definition tree_adder n a
  : << Vector (Vector Bit (S a)) (2^n), Unit >> ~> (Vector Bit (S a)) :=
  <[ \ v => !(tree (Vector Bit (S a)) n (xilinxAdder a)) v  ]>.

  Definition adder_large: << Vector (Vector Bit 256) 1, Unit >> ~> (Vector Bit 256)
    := tree_adder 0 _.
End notation.


Require Import Cava.Types.
Require Import Cava.Netlist.

(* Definition fullAdderInterface *)
(*   := combinationalInterface "fullAdder" *)
(*      (mkPort "cin" Kind.Bit, (mkPort "a" Kind.Bit, mkPort "b" Kind.Bit)) *)
(*      (mkPort "sum" Kind.Bit, mkPort "cout" Kind.Bit) *)
(*      []. *)

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
  build_netlist (closure_conversion fullAdder) "fullAdder" ("cin", ("a", "b")) ("sum", "cout").

Definition fullAdder_tb_expected_outputs  : list (bool * bool)
  := (List.map (fun i => interp_combinational (module_to_expr fullAdder _) i) fullAdder_tb_inputs) .

Definition fullAdderInterface
  := combinationalInterface "fullAdder"
     [mkPort "cin" Signal.Bit; mkPort "a" Signal.Bit; mkPort "b" Signal.Bit]
     [mkPort "sum" Signal.Bit; mkPort "cout" Signal.Bit]
     [].

Definition fullAdder_tb :=
  testBench "fullAdder_tb" fullAdderInterface
            (map (fun '(a,(b,c)) => (a,b,c)) fullAdder_tb_inputs) fullAdder_tb_expected_outputs.


Import EqNotations.

Fixpoint collapse_rewrites {i o}
  (c: Circuit i o)
  : Circuit i o.
  refine (
    match c in Circuit i o return Circuit i o with
  | @Composition x y z f g =>
    match f in Circuit x' y' return Circuit x z with
    | RewriteTy _ _ =>
          match eq_kind_dec x y with
          | left e => rew <- [fun y1 : Kind => Circuit y1 z] e in g
          | right _ => Composition (collapse_rewrites _ _ f) (collapse_rewrites _ _ g)
          end
    | _ =>
      match g in Circuit y' z' return Circuit x z with
      | RewriteTy _ _ =>
            match eq_kind_dec y z with
            | left e => rew [fun y1 : Kind => Circuit x y1] e in f
            | right _ => Composition (collapse_rewrites _ _ f) (collapse_rewrites _ _ g)
            end
      | _ => Composition (collapse_rewrites _ _ f) (collapse_rewrites _ _ g)
      end
    end
  | First _ f => First _ (collapse_rewrites _ _ f)
  | Second _ f => Second _ (collapse_rewrites _ _ f)
  | @Loopr _ _ Z f => Loopr (collapse_rewrites _ _ f)
  | @Loopl _ _ Z f => Loopl(collapse_rewrites _ _ f)
  | x => x
end).
Defined.

Definition collapse_rewrites1 {i o}
  (c: TopCircuit i o) :=
  mkTop
    (map (fun '(existT _ (i,o) c) => existT _ (i,o) (collapse_rewrites c)) (fragments c))
    (collapse_rewrites (toplevel c)).

Definition adder_large_netlist :=
  build_netlist (collapse_rewrites1 (closure_conversion adder_large)) "adderLarge" "vec" "result".


Fixpoint test {i o}
  (c: Circuit i o)
  : nat :=
    match c with
  | Composition f g => test f + test g
  | First _ f => test f
  | Second _ f => test f
  | @Loopr _ _ Z f => test f
  | @Loopl _ _ Z f => test f

  | RewriteTy x y => 1
  | _ => 0
end.

Compute test (toplevel (collapse_rewrites1 (closure_conversion adder_large))).
Compute
  (* map (fun '(existT _ (i,o) c) => test c) *)
length
  (fragments (collapse_rewrites1 (closure_conversion (xilinxAdder 128)))).
(* Compute test (collapse_rewrites (toplevel (closure_conversion adder_large))). *)
(* Compute length (fragments (closure_conversion adder_large)). *)

