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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From ArrowExamples Require Import Combinators Aes.pkg Aes.sbox_canright_pkg.

Inductive circuit_equiv: forall i o, Circuit i o -> (denote_kind i -> denote_kind o) -> Prop :=
  | Composition_equiv: forall x y z c1 c2 r1 r2 r,
    circuit_equiv x y c1 r1 ->
    circuit_equiv y z c2 r2 ->
    (forall a:denote_kind x, r a = r2 (r1 a) ) ->
    circuit_equiv x z (Composition _ _ _ c1 c2) r

  | Uncancell_equiv: forall x,
    circuit_equiv x (Tuple Unit x) (Structural (Uncancell x)) (fun a => (tt, a))
  | Uncancelr_equiv: forall x,
    circuit_equiv x (Tuple x Unit) (Structural (Uncancelr x)) (fun a => (a, tt))

  | Cancell_equiv: forall x,
    circuit_equiv (Tuple Unit x) x (Structural (Cancell x)) (fun a => snd a)
  | Cancelr_equiv: forall x,
    circuit_equiv (Tuple x Unit) x (Structural (Cancelr x)) (fun a => fst a)

  | First_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    forall a, r a = (r1 (fst a), snd a) ->
    circuit_equiv (Tuple x z) (Tuple y z) (First x y z c) r

  | Second_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    forall a, r a = (fst a, r1 (snd a)) ->
    circuit_equiv (Tuple z x) (Tuple z y) (Second x y z c) r

  | Swap_equiv: forall x y,
    circuit_equiv (Tuple x y) (Tuple y x) (Structural (Swap x y)) (fun a => (snd a, fst a))
  | Drop_equiv: forall x,
    circuit_equiv x Unit (Structural (Drop x)) (fun a => tt)
  | Copy_equiv: forall x,
    circuit_equiv x (Tuple x x) (Structural (Copy x)) (fun a => (a,a))

  | Assoc_equiv: forall x y z,
    circuit_equiv (Tuple (Tuple x y) z) (Tuple x (Tuple y z))
    (Structural (Assoc x y z)) (fun i => (fst (fst i), (snd (fst i), snd i)))
  | Unassoc_equiv: forall x y z,
    circuit_equiv (Tuple x (Tuple y z)) (Tuple (Tuple x y) z)
    (Structural (Unassoc x y z)) (fun i => ((fst i, fst (snd i)), snd (snd i)))

  | Id_equiv: forall x,
    circuit_equiv x x (Structural (Arrow.Id x)) (fun a => a)

  | Map_equiv: forall x y n c r r1,
    circuit_equiv x y c r1 ->
    (forall v, r v = Vector.map r1 v) ->
    circuit_equiv (Vector x n) (Vector y n) (Map x y n c) r

  | Resize_equiv: forall x n nn,
    circuit_equiv (Vector x n) (Vector x nn) (Resize x n nn)
      (fun v => resize_default (kind_default _) nn v)

  | Primtive_equiv: forall p,
    circuit_equiv (primitive_input p) (primitive_output p) (CircuitArrow.Primitive p) (combinational_evaluation' (CircuitArrow.Primitive p))
  .

(*   (1* contains subcircuits *1) *)
(*   | First: forall x y z, Circuit x y -> Circuit (Tuple x z) (Tuple y z) *)
(*   | Second: forall x y z, Circuit x y -> Circuit (Tuple z x) (Tuple z y) *)
(*   | Loopr: forall x y z, Circuit (Tuple x z) (Tuple y z) -> Circuit x y *)
(*   | Loopl: forall x y z, Circuit (Tuple z x) (Tuple z y) -> Circuit x y *)

(*   | Map: forall x y n, Circuit x y -> Circuit (Vector x n) (Vector y n) *)
(*   | Resize: forall x n nn, Circuit (Vector x n) (Vector x nn) *)

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* function automatic logic [3:0] aes_inverse_gf2p4(logic [3:0] gamma);
  logic [3:0] delta;
  logic [1:0] a, b, c, d;
  a          = gamma[3:2] ^ gamma[1:0];
  b          = aes_mul_gf2p2(gamma[3:2], gamma[1:0]);
  c          = aes_scale_omega2_gf2p2(aes_square_gf2p2(a));
  d          = aes_square_gf2p2(c ^ b);
  delta[3:2] = aes_mul_gf2p2(d, gamma[1:0]);
  delta[1:0] = aes_mul_gf2p2(d, gamma[3:2]);
  return delta;
endfunction *)
Program Definition aes_inverse_gf2p4
  :  <<Vector Bit 4, Unit>> ~> (Vector Bit 4) :=
  <[\ gamma =>
      let a = (gamma[:3:2]) ^ (gamma[:1:0]) in
      let b = !aes_mul_gf2p2 (gamma[:3:2]) (gamma[:1:0]) in
      let c = !aes_scale_omega2_gf2p2 (!aes_square_gf2p2 a) in
      let d = !aes_square_gf2p2 (c ^ b) in
      concat
        (!aes_mul_gf2p2 d (gamma[:3:2]))
        (!aes_mul_gf2p2 d (gamma[:1:0]))
  ]>.

  (* // Inverse in GF(2^8), using normal basis [d^16, d]
  // (see Figure 11 in the technical report)
  function automatic logic [7:0] aes_inverse_gf2p8(logic [7:0] gamma);
    logic [7:0] delta;
    logic [3:0] a, b, c, d;
    a          = gamma[7:4] ^ gamma[3:0];
    b          = aes_mul_gf2p4(gamma[7:4], gamma[3:0]);
    c          = aes_square_scale_gf2p4_gf2p2(a);
    d          = aes_inverse_gf2p4(c ^ b);
    delta[7:4] = aes_mul_gf2p4(d, gamma[3:0]);
    delta[3:0] = aes_mul_gf2p4(d, gamma[7:4]);
    return delta;
  endfunction *)
Definition aes_inverse_gf2p8
  :  <<Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ gamma =>
      let a = (gamma[:7:4]) ^ (gamma[:3:0]) in
      let b = !aes_mul_gf2p4 (gamma[:7:4]) (gamma[:3:0]) in
      let c = !aes_square_scale_gf2p4_gf2p2 a in
      let d = !aes_inverse_gf2p4 (c ^ b) in

      concat
        (!aes_mul_gf2p4 d (gamma[:7:4]))
        (!aes_mul_gf2p4 d (gamma[:3:0]))
  ]>.

(* module aes_sbox_canright (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
); *)
Definition aes_sbox_canright
  :  << Bit, Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ op_i data_i =>
      (* // Convert to normal basis X.
      assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                                aes_mvm(data_i ^ 8'h63, S2X); *)
      let data_basis_x = if op_i == !CIPH_FWD
                        then !aes_mvm data_i !A2X
                        else !aes_mvm (data_i ^ #99) !S2X in

      (* // Do the inversion in normal basis X.
      assign data_inverse = aes_inverse_gf2p8(data_basis_x); *)
      let data_inverse = !aes_inverse_gf2p8 data_basis_x in

      (* // Convert to basis S or A.
      assign data_o       = (op_i == CIPH_FWD) ? aes_mvm(data_inverse, X2S) ^ 8'h63 :
                                                aes_mvm(data_inverse, X2A);  *)
      let data_o = if op_i == !CIPH_FWD
                  then (!aes_mvm data_inverse !X2S) ^ #99
                  else !aes_mvm data_inverse !X2A in

      data_o
  ]>.

Definition canright_composed
  :  << Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\input =>
  let encoded = !aes_sbox_canright !CIPH_FWD input in
  let decoded = !aes_sbox_canright !CIPH_INV encoded in
  decoded ]>.

(* Lemma canright_composed_combinational: is_combinational (closure_conversion aes_sbox_canright).
Proof. time simply_combinational. Qed. *)




Goal exists r, circuit_equiv _ _ (closure_conversion canright_composed) r.
Proof.
  intros.
  eexists.

  cbv [
    closure_conversion' closure_conversion canright_composed
    cancell cancelr uncancell uncancelr assoc unassoc first second copy drop swap compose
    CircuitCat CircuitArrow CircuitArrowSwap CircuitArrowDrop CircuitArrowCopy
    arrow_category
    as_kind

    Datatypes.length Nat.eqb extract_nth rewrite_or_default
  ].
econstructor.
econstructor.
econstructor.
econstructor.
econstructor.

  cbv beta.
  Set Printing Implicit.
  cbn [denote_kind product].

  instantiate (5:= fun (x: (t bool 8 * unit * unit)) => (Datatypes.snd (Datatypes.fst x), Datatypes.fst (Datatypes.fst x), Datatypes.snd x)).
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  cbv beta.
  instantiate (3:= fun x => (tt, Datatypes.snd x)).
  cbv beta.
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  cbv beta.
  instantiate (3:= fun x => (Datatypes.fst x, tt)).
  cbv beta.
  reflexivity.

  econstructor.
  econstructor.
  econstructor.
  econstructor.


  econstructor.
  econstructor.
  econstructor.

  all:
    intros;
    cbv beta;
    try reflexivity.


  intros.
  cbv beta.
  cbn [Datatypes.fst Datatypes.snd].

  Ltac t :=
    lazymatch goal with
    | |- ?lhs = ?rhs =>
      lazymatch lhs with
      | ?g ?x =>
        lazymatch rhs with
        | context[combinational_evaluation'] => fail "Contains combinational_evaluation'"rhs
        | _ =>
          match (eval pattern x in rhs) with
          | ?f _ =>
            let H := fresh in
            assert (forall y, f y = g y) as H;
            [ intros; reflexivity | apply H ]
          end
        end
      end
    | |- circuit_equiv _ _ _ _ => econstructor; intros
    | _ => fail "No go!"
    end.
  t. t. t. t.
  t. t. t. t.
  t. t. t. t.
  t. t. t. t.
  t. t. t. t.
  t. t.
  t.


  intros.


  t.
  cbn [].

  t.
  t. t.
  t. t.












  cbv [
    closure_conversion' closure_conversion canright_composed
    cancell cancelr uncancell uncancelr assoc unassoc first second copy drop swap compose
    CircuitCat CircuitArrow CircuitArrowSwap CircuitArrowDrop CircuitArrowCopy
    arrow_category
    denote_destruct proj_i proj_o denote_kind as_kind product
  ].
  simpl in * |- .
  destruct x.
  eexists.


  constructor.
  eexists.
  destruct d.
  intros.
eexists.
  eexists.
destuct



Proof. time (vm_compute; auto). Qed.

Lemma canright_composed_combinational: is_combinational (closure_conversion aes_sbox_canright).
Proof. time simply_combinational. Qed.

Local Notation "# x" := (nat_to_bitvec_sized 8 x) (at level 99).

Goal interp_combinational (canright_composed _) (# 0) = (# 0).
Proof. time (vm_compute; auto). Qed.

(* TODO(blaxill): reduced bound for CI time *)
Goal forall x, x < 100 ->
interp_combinational (canright_composed _) (#x) = (#x).
Proof. time (repeat (lia || destruct x); now vm_compute). Qed.

