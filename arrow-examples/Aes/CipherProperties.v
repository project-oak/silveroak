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

Require Import Coq.Strings.String.
From Coq Require Import Derive.
From Cava Require Import Arrow.ArrowExport Arrow.CircuitFunctionalEquivalence
     BitArithmetic Tactics VectorUtils.

From ArrowExamples Require Import CombinatorProperties Aes.cipher_round Aes.unrolled_naive_cipher.

Module Vector.
  (* matches pkg.aes_transpose; uses snoc/unsnoc instead of cons/tl *)
  Fixpoint transpose_rev {A n m} : Vector.t (Vector.t A m) n -> Vector.t (Vector.t A n) m :=
    match n with
    | O => fun _ => Vector.const (Vector.nil _) _
    | S n' =>
      fun mat =>
        let r := unsnoc mat in
        let mat' := fst r in
        let vec := snd r in
        Vector.map2 snoc (transpose_rev mat') vec
    end.

  (* Alternate version of vtranspose_rev *)
  Fixpoint transpose {A n m}
    : Vector.t (Vector.t A n) m -> Vector.t (Vector.t A m) n :=
    match m with
    | 0 => fun _ => Vector.const (Vector.nil _) _
    | S m' =>
      fun v : Vector.t (Vector.t A n) (S m') =>
        Vector.map2 (fun x v => Vector.cons _ x m' v)
                    (Vector.hd v) (transpose (Vector.tl v))
    end.

  Lemma fold_left_ext {A B} (f g : B -> A -> B) n b v :
    (forall b a, f b a = g b a) ->
    @Vector.fold_left A B f b n v = Vector.fold_left g b v.
  Proof.
    intro Hfg. revert b.
    induction n; intros; autorewrite with push_vector_fold;
      [ reflexivity | ].
    rewrite IHn, Hfg. reflexivity.
  Qed.
End Vector.

Local Ltac derived_spec_done :=
  lazymatch goal with
  | |- context [interp_combinational' ?x] =>
    fail "derived spec still contains disallowed term: interp_combinational'" x
  | _ => idtac
  end;
  repeat match goal with
         | x := _ |- _ => subst x
         end;
  instantiate_app_by_reflexivity.

Local Ltac spec_simplify :=
  repeat match goal with
         | |- context [let '(x, _) := ?p in x] =>
           change (let '(x, _) := p in x) with (fst p)
         | |- context [let '(_, x) := ?p in x] =>
           change (let '(_, x) := p in x) with (snd p)
         end.
Local Ltac derive_spec :=
  match goal with
  | |- context [interp_combinational'] => idtac
  | |- ?x => fail "goal does not include interp_combinational:" x
  end;
  intros; spec_simplify; kappa_spec; derived_spec_done.

Section NaiveCipher.
  Context {CircuitLaws : CategoryLaws CircuitCat}.

  Lemma aes_transpose_correct n m (x : Vector.t (Vector.t (Vector.t bool _) _) _) :
    kinterp (@pkg.aes_transpose n m) (x, tt) = Vector.transpose_rev x.
  Proof.
    revert m x; induction n; cbn [pkg.aes_transpose Vector.transpose_rev];
      kappa_spec; [ reflexivity | ].
    repeat destruct_pair_let. cbn [fst snd].
    autorewrite with vsimpl. reflexivity.
  Qed.
  Hint Rewrite @aes_transpose_correct : kappa_interp.
  Opaque pkg.aes_transpose.

  Axiom aes_256_naive_key_expansion_spec :
    pkg.SboxImpl ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 8 ->
    (Vector.t (Vector.t (Vector.t (Vector.t bool 8) 4) 4) 15).
  Axiom aes_256_naive_key_expansion_correct :
    forall sbox_impl key,
      kinterp (aes_256_naive_key_expansion sbox_impl) (key, tt) =
      aes_256_naive_key_expansion_spec sbox_impl key.
  Hint Rewrite @aes_256_naive_key_expansion_correct : kappa_interp.
  Opaque aes_256_naive_key_expansion.

  Axiom cipher_round_spec :
    pkg.SboxImpl -> bool ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4 ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4 ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4.
  Axiom cipher_round_correct :
    forall sbox_impl op_i_state key,
      kinterp
        (Combinators.curry (cipher_round sbox_impl)) (op_i_state, (key, tt))
      = cipher_round_spec sbox_impl (fst op_i_state) (snd op_i_state) key.
  Hint Rewrite @cipher_round_correct : kappa_interp.
  Opaque cipher_round.

  Axiom final_cipher_round_spec :
    pkg.SboxImpl -> bool ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4 ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4 ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4.
  Axiom final_cipher_round_correct :
    forall sbox_impl op_i state key,
      kinterp (final_cipher_round sbox_impl) (op_i, (state, (key, tt)))
      = final_cipher_round_spec sbox_impl op_i state key.
  Hint Rewrite @final_cipher_round_correct : kappa_interp.
  Opaque final_cipher_round.

  Axiom aes_mix_columns_spec :
    bool ->  Vector.t (Vector.t (Vector.t bool 8) 4) 4 ->
    Vector.t (Vector.t (Vector.t bool 8) 4) 4.
  Axiom aes_mix_columns_correct :
    forall op_i state,
      kinterp mix_columns.aes_mix_columns (op_i, (state, tt)) = aes_mix_columns_spec op_i state.
  Hint Rewrite @aes_mix_columns_correct : kappa_interp.
  Opaque mix_columns.aes_mix_columns.

  Axiom CIPH_FWD_correct :
    interp_combinational' (pkg.CIPH_FWD coq_func) tt = false.
  Axiom CIPH_INV_correct :
    interp_combinational' (pkg.CIPH_INV coq_func) tt = true.
  Hint Rewrite @CIPH_FWD_correct @CIPH_INV_correct : kappa_interp.
  Opaque pkg.CIPH_FWD pkg.CIPH_INV.


  Derive unrolled_cipher_naive'_spec
         SuchThat (forall (sbox_impl : pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t (Vector.t bool 8) 4) 4)
                     (key : Vector.t (Vector.t (Vector.t bool 8) 4) 8),
                      kinterp (unrolled_cipher_naive' sbox_impl)
                              (op_i, (data, (key, tt)))
                      = unrolled_cipher_naive'_spec sbox_impl op_i data key)
         As unrolled_cipher_naive'_spec_correct.
  Proof.
    cbv [unrolled_cipher_naive']; kappa_spec.
    repeat destruct_pair_let.
    repeat match goal with
           | |- context [Vector.map ?f] =>
             erewrite (Vector.map_ext _ _ f) by derive_spec
           | |- context [Vector.fold_left ?f] =>
             erewrite (Vector.fold_left_ext f) by derive_spec
           end.
    derived_spec_done.
  Qed.
  Hint Rewrite @unrolled_cipher_naive'_spec_correct : kappa_interp.
  Opaque unrolled_cipher_naive'.

  Derive unrolled_cipher_naive_spec
         SuchThat
         (forall sbox_impl op_i (data : Vector.t bool 128) (key : Vector.t bool 256),
            kinterp (unrolled_cipher_naive sbox_impl) (op_i, (data, (key, tt)))
            = unrolled_cipher_naive_spec sbox_impl op_i data key)
         As unrolled_cipher_naive_correct.
  Proof. cbv [unrolled_cipher_naive]. derive_spec. Qed.
End NaiveCipher.
