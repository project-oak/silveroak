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

From Coq Require Import Strings.String Bvector List NArith Nat Lia Plus.
Import ListNotations.
Import EqNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.

  Section var.
    Variable var: Kind -> Kind -> Type.

    Definition rewrite_vector {A x y} (H: x = y)
      : CavaExpr var << Vector A x, Unit >> <<Vector A y>>
      :=
    match PeanoNat.Nat.eq_dec x y with
    | left Heq =>
      rew [fun x => CavaExpr var << _, _ >> <<Vector A x>> ] Heq in Id
    | right Hneq => (ltac:(exfalso;contradiction))
    end.

    Definition rewrite_kind {x y} (H: x = y)
      : CavaExpr var << x, Unit >> y
      :=
    match decKind x y with
    | left Heq =>
      rew [fun x => CavaExpr var << _ >> <<x>> ] Heq in Id
    | right Hneq => (ltac:(exfalso;contradiction))
    end.

    Definition unsigned_adder a b c
    : CavaExpr var << Vector Bit a, Vector Bit b, Unit >> (Vector Bit c) :=
    <[ \ x y => unsigned_add a b c x y ]>.

    Definition adder3 s1 s2 s3
    : CavaExpr var << Vector Bit s1, Vector Bit s2, Vector Bit s3, Unit >> (Vector Bit _) :=
    <[ \ a b c => a + b + c ]>.

    Definition split_pow2 A n
      : CavaExpr var << Vector A (2^(S n)), Unit >> <<Vector A (2^n), Vector A (2^n)>>.
      refine (<[\ x => 
        let '(l,r) = split_at (2^n) x in
        (l, !(rewrite_vector _) r)
         ]>);
      induction n; simpl; auto; nia.
    Defined.

    Fixpoint tree (A: Kind) (n: nat)
      (f: CavaExpr var << A, A, Unit >> A) {struct n}
      : CavaExpr var << Vector A (2^(n+1)), Unit >> A :=
    match n with
    | O => <[ \ vec =>
        let '(a,vec') = uncons vec in
        let '(b,_) = uncons vec' in
        !f a b
      ]>
    | S n' => 
      <[\ x =>
          let '(left,right) = !(split_pow2 A (n'+1)) x in
          let a = !(tree A n' f) left in
          let b = !(tree A n' f) right in
          !f a b
      ]>
    end.

    Definition tree_adder a n
    : CavaExpr var << Vector (Vector Bit a) (2^(n+1)), Unit >> (Vector Bit a) :=
    <[ \ v => !(tree (Vector Bit a) n (unsigned_adder a a a)) v  ]>.

    Fixpoint dt_tree_fold'
      (n k: nat)
      (T: nat -> Kind)
      (f: forall n, CavaExpr var << T n, T n, Unit >> (T (S n))) {struct n}
      : CavaExpr var << Vector (T k) (2^(n + 1)), Unit >> (T (S (n + k))) :=
    match n with
    | O => 
      <[ \ vec =>
        let '(a,vec') = uncons vec in
        let '(b,_) = uncons vec' in
        !(rewrite_kind (ltac:(auto))) (!(f k) a b)
      ]>
    | S n' =>  
      <[\ x =>
          let '(left,right) = !(split_pow2 (T k) (n'+1)) x in
          let a = !(dt_tree_fold' n' k T f) left in
          let b = !(dt_tree_fold' n' k T f) right in
          !(f _) a b
      ]>
    end.

    Definition dt_tree_fold
      (n: nat)
      (T: nat -> Kind)
      (f: forall n, CavaExpr var << T n, T n, Unit >> (T (S n))) 
      : CavaExpr var << Vector (T 0) (2^(n + 1)), Unit >> (T (S n)) :=
      match PeanoNat.Nat.eq_dec (S (n + 0)) (S n) with
      | left Heq => rew [fun x => CavaExpr var <<_>> <<T x>> ] Heq in dt_tree_fold' n 0 T f
      | right Hneq => (ltac:(exfalso; abstract lia))
      end.

    Lemma max_nn_add_1_is_S_n: forall n, 1 + max n n = S n.
    Proof. intros; rewrite PeanoNat.Nat.max_id; auto. Qed.

    Definition growth_adder n 
    : CavaExpr var << Vector Bit n, Vector Bit n, Unit >> (Vector Bit (S n)) :=
    <[ \ a b => !(rewrite_vector (max_nn_add_1_is_S_n _)) (a + b) ]>.

    Definition growth_tree_adder a n
    : CavaExpr var << Vector (Vector Bit a) (2^(n+1)), Unit >> (Vector Bit (S (n + a)) ) :=
    <[ \ v => !(dt_tree_fold' n a (Vector Bit) (growth_adder)) v  ]>.

  End var.

End notation.

Open Scope kind_scope.
Definition adder445 {cava: Cava}: 
    << Vector Bit 4, Vector Bit 4 >> ~[cava]~> (Vector Bit 5) 
  := to_arrow (fun var => unsigned_adder var 4 4 5).

Lemma adder445_is_combinational: wf_combinational adder445.
Proof. combinational_obvious. Qed.

Definition adder88810 {cava: Cava}: 
    << Vector Bit 8, Vector Bit 8, Vector Bit 8 >> ~[cava]~> (Vector Bit 10) 
  := to_arrow (fun var => adder3 var 8 8 8).

Lemma adder88810_is_combinational: wf_combinational adder88810.
Proof. combinational_obvious. Qed.

Lemma adder_tree_4_wf: forall (cava:Cava), wf_debrujin [] (desugar (tree_adder _ 4 1)).
Proof. compute; tauto. Qed.
Lemma adder_tree_8_wf: forall (cava:Cava), wf_debrujin [] (desugar (tree_adder _ 4 2)).
Proof. compute; tauto. Qed.
Lemma adder_tree_64_wf: forall (cava:Cava), wf_debrujin [] (desugar (tree_adder _ 4 5)).
Proof. compute; tauto. Qed.

Lemma growth_tree_8_wf: forall (cava:Cava), wf_debrujin [] (desugar (growth_tree_adder _ 4 2)).
Proof. compute; tauto. Show Proof. Qed.

Definition adder444_tree_4 {cava: Cava}: 
  << Vector (Vector Bit 4) 4 >> ~[cava]~> (Vector Bit 4) 
  := insert_rightmost_tt1 _ >>> Arrow.uncancelr >>> 
  (closure_conversion' (object_decidable_equality:=decKind) []
    (desugar (tree_adder _ 4 1))
    (adder_tree_4_wf cava)).
Definition adder444_tree_8 {cava: Cava}: 
  << Vector (Vector Bit 4) 8 >> ~[cava]~> (Vector Bit 4) 
  := insert_rightmost_tt1 _ >>> Arrow.uncancelr >>> 
  closure_conversion' (object_decidable_equality:=decKind) []
  ((desugar (tree_adder _ 4 2)))
  (adder_tree_8_wf cava).
Definition adder444_tree_64 {cava: Cava}: 
  << Vector (Vector Bit 4) 64 >> ~[cava]~> (Vector Bit 4) 
  := insert_rightmost_tt1 _ >>> Arrow.uncancelr >>> 
  closure_conversion' (object_decidable_equality:=decKind) []
  ((desugar (tree_adder _ 4 5)))
  (adder_tree_64_wf  cava).

Definition growth_tree_8 {cava: Cava}: 
  << Vector (Vector Bit 4) 8>> ~[cava]~> (Vector Bit 7) 
  := insert_rightmost_tt1 _ >>> Arrow.uncancelr >>> 
  (closure_conversion' (object_decidable_equality:=decKind) []
    (desugar (growth_tree_adder _ 4 2))
    (growth_tree_8_wf cava)).

Require Import Cava.Types.
Require Import Cava.Netlist.

Definition adder445_interface
  := combinationalInterface "adder445"
     (mkPort "a" (Kind.BitVec Kind.Bit 4), mkPort "b" (Kind.BitVec Kind.Bit 4))
     (mkPort "sum" (Kind.BitVec Kind.Bit 5))
     [].
Definition adder88810_interface 
  := combinationalInterface "adder88810"
     (mkPort "a" (Kind.BitVec Kind.Bit 8), (mkPort "b" (Kind.BitVec Kind.Bit 8), mkPort "c" (Kind.BitVec Kind.Bit 8)))
     (mkPort "sum" (Kind.BitVec Kind.Bit 10))
     [].
Definition adder444_tree_4_interface 
  := combinationalInterface "adder444_tree_4"
     (mkPort "vec" (Kind.BitVec (Kind.BitVec Kind.Bit 4) 4))
     (mkPort "result" (Kind.BitVec Kind.Bit 4))
     [].
Definition adder444_tree_8_interface 
  := combinationalInterface "adder444_tree_8"
     (mkPort "vec" (Kind.BitVec (Kind.BitVec Kind.Bit 4) 8))
     (mkPort "result" (Kind.BitVec Kind.Bit 4))
     [].
Definition adder444_tree_64_interface 
  := combinationalInterface "adder444_tree_64"
     (mkPort "vec" (Kind.BitVec (Kind.BitVec Kind.Bit 4) 64))
     (mkPort "result" (Kind.BitVec Kind.Bit 4))
     [].
Definition growth_tree_8_interface 
  := combinationalInterface "growth_tree_8"
     (mkPort "vec" (Kind.BitVec (Kind.BitVec Kind.Bit 4) 8))
     (mkPort "result" (Kind.BitVec Kind.Bit 7))
     [].

Definition adder445_netlist :=
  makeNetlist adder445_interface (arrow_netlist adder445).

Definition adder445_tb_inputs :=
  map (fun '(x, y) => (N2Bv_sized 4 x, N2Bv_sized 4 y))
  [(0, 0); (1, 2); (15, 1); (15, 15)]%N.

Definition adder445_tb_expected_outputs
  := map (fun i => evaluate adder445 adder445_is_combinational i) adder445_tb_inputs.

Definition adder445_tb
  := testBench "adder445_tb" adder445_interface
     adder445_tb_inputs adder445_tb_expected_outputs.

Definition adder88810_netlist :=
  makeNetlist adder88810_interface (arrow_netlist adder88810).

Definition adder88810_tb_inputs :=
  map (fun '(x, y, z) => (N2Bv_sized 8 x, (N2Bv_sized 8 y, N2Bv_sized 8 z)))
  [(17, 23, 95); (4, 200, 30); (255, 255, 200)]%N.

Definition adder88810_tb_expected_outputs
  := map (fun i => evaluate adder88810 adder88810_is_combinational i) adder88810_tb_inputs.

Definition adder88810_tb
  := testBench "adder88810_tb" adder88810_interface
     adder88810_tb_inputs adder88810_tb_expected_outputs.

Definition adder444_tree_4_netlist :=
  makeNetlist adder444_tree_4_interface (arrow_netlist adder444_tree_4).

Definition adder444_tree_8_netlist :=
  makeNetlist adder444_tree_8_interface (arrow_netlist adder444_tree_8).

Definition adder444_tree_64_netlist :=
  makeNetlist adder444_tree_64_interface (arrow_netlist adder444_tree_64).

Definition adder444_tree_4_inputs :=
  map (fun '(x, y, z, w) => [N2Bv_sized 4 x; N2Bv_sized 4 y; N2Bv_sized 4 z; N2Bv_sized 4 w]%vector)
  [(0, 0, 0, 1); (1, 1, 1, 1); (1, 3, 5, 2); (15, 1, 1, 1)]%N.

Lemma adder444_tree_4_is_combinational: wf_combinational adder444_tree_4.
Proof. combinational_obvious. Qed.

Definition adder444_tree_4_tb_expected_outputs
  := map (fun i => evaluate adder444_tree_4 adder444_tree_4_is_combinational i) adder444_tree_4_inputs.

Definition adder444_tree_4_tb
  := testBench "adder444_tree_4_tb" adder444_tree_4_interface
     adder444_tree_4_inputs adder444_tree_4_tb_expected_outputs.

Definition growth_tree_8_netlist :=
  makeNetlist growth_tree_8_interface (arrow_netlist growth_tree_8).

Definition growth_tree_8_inputs :=
  map (Vector.map (N2Bv_sized 4))
  [[0; 0; 0; 0; 0; 0; 0; 1]%vector %N
  ;[1; 1; 1; 1; 1; 1; 1; 1]%vector %N
  ;[1; 2; 3; 4; 5; 6; 7; 8]%vector %N
  ;[15; 15; 15; 15; 15; 15; 15; 15]%vector %N
  ].

Lemma growth_tree_8_is_combinational: wf_combinational growth_tree_8.
Proof. combinational_obvious. Qed.

Definition growth_tree_8_tb_expected_outputs
  := map (fun i => evaluate growth_tree_8 growth_tree_8_is_combinational i) growth_tree_8_inputs.

Definition growth_tree_8_tb
  := testBench "growth_tree_8_tb" growth_tree_8_interface
     growth_tree_8_inputs growth_tree_8_tb_expected_outputs.