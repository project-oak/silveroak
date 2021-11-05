(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Types.

Lemma step_vec_as_tuple_cons {t n} (xs : list (denote_type t)) :
  step (vec_as_tuple (t:=t) (n:=S n)) tt (xs, tt)
  = (tt, (hd default xs, snd (step (vec_as_tuple (t:=t) (n:=n)) tt (tl xs, tt)))).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_cons using solve [eauto] : stepsimpl.

Lemma step_vec_as_tuple_one {t} (xs : list (denote_type t)):
  step (vec_as_tuple (t:=t) (n:=0)) tt (xs, tt) = (tt, hd default xs).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_one using solve [eauto] : stepsimpl.

Ltac stepsimpl :=
  repeat first [ progress
                   cbn [fst snd step denote_type absorb_any One Zero K
                            split_absorbed_denotation combine_absorbed_denotation
                            unary_semantics binary_semantics eqb ]
               | progress autorewrite with stepsimpl ].

Lemma step_index {t n i} (x : denote_type (Vec t n))
      (idx : denote_type (BitVec i)) :
  step (@index _ t n i) tt (x, (idx, tt))
  = (tt, nth (N.to_nat idx) (List.resize default n x) default).
Proof. reflexivity. Qed.
Hint Rewrite @step_index using solve [eauto] : stepsimpl.

Lemma step_uncons {t n}  (x : denote_type [Vec t (S n)]) :
  step (@uncons _ t n) tt x = (tt, (hd default (fst x), tl (fst x))).
Proof. destruct x; reflexivity. Qed.
Hint Rewrite @step_uncons using solve [eauto] : stepsimpl.

Lemma step_stateless {i o} (f : Circuit [] i o) (x : denote_type i) :
  step f tt x = (tt, snd (step f tt x)).
Proof.
  rewrite (surjective_pairing (step f tt x)).
  destruct (fst (step f tt x)). reflexivity.
Qed.

Lemma step_map2 {t u v n} (f : Circuit [] [t;u] v)
      (x : denote_type [Vec t n; Vec u n]) :
  step (@Expr.map2 _ t u v n f) tt x
  = (tt, List.map2 (fun (x1 : denote_type t) (x2 : denote_type u) =>
                      snd (step f tt (x1,(x2,tt))))
                   (List.resize default n (fst x))
                   (List.resize default n (fst (snd x)))).
Proof.
  revert x f; induction n; cbn [Expr.map2]; stepsimpl;
    intros; destruct_products; logical_simplify; stepsimpl;
      [ rewrite resize_0; reflexivity | ].
  rewrite step_stateless, IHn.
  rewrite !resize_succ. reflexivity.
Qed.
Hint Rewrite @step_map2 using solve [eauto] : stepsimpl.

Lemma step_bvresize {n m} (x : denote_type (BitVec n)) :
  step (bvresize (n:=n) m) tt (x, tt) = (tt, N.land x (N.ones (N.of_nat m))).
Proof. reflexivity. Qed.
Hint Rewrite @step_bvresize using solve [eauto] : stepsimpl.

Lemma step_bvconcat {n m} (x : denote_type (BitVec n)) (y : denote_type (BitVec m)) :
  step (bvconcat (n:=n) (m:=m)) tt (x, (y, tt))
  = (tt, N.lor (N.shiftl (N.land x (N.ones (N.of_nat n))) (N.of_nat m))
               (N.land y (N.ones (N.of_nat (n + m))))).
Proof.
  cbv [bvconcat]. stepsimpl. f_equal.
  apply N.bits_inj; intro i. push_Ntestbit.
  rewrite Nat2N.inj_add.
  destruct_one_match; push_Ntestbit; boolsimpl; [ | reflexivity ].
  destr (i <? N.of_nat m)%N; push_Ntestbit; boolsimpl; reflexivity.
Qed.
Hint Rewrite @step_bvconcat using solve [eauto] : stepsimpl.

Lemma step_bvslice {n start len} (x : denote_type (BitVec n)) :
  step (bvslice (n:=n) start len) tt (x, tt)
  = (tt, N.land (N.shiftr x (N.of_nat start)) (N.ones (N.of_nat len))).
Proof. reflexivity. Qed.
Hint Rewrite @step_bvslice using solve [eauto] : stepsimpl.

Lemma step_foldl {t u n}
      (f : Circuit [] [t;u] t)
      (v : denote_type (Vec u n)) (x : denote_type t) :
  step (foldl (n:=n) f) tt (v, (x, tt))
  = (tt, List.fold_left
           (A:=denote_type t) (B:=denote_type u)
           (fun t u => snd (step f tt (t,(u,tt))))
           (List.resize default n v) x).
Proof.
  revert x; induction n; cbn [denote_type] in *; intros;
    cbn [foldl]; stepsimpl; push_resize; push_list_fold;
      [ reflexivity | ].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite IHn. cbn [fst snd].
  rewrite resize_succ. push_list_fold.
  reflexivity.
Qed.
Hint Rewrite @step_foldl using solve [eauto] : stepsimpl.

Lemma step_foldl2 {t u v n}
      (f : Circuit [] [t;u;v] t)
      (v1 : denote_type (Vec u n))
      (v2 : denote_type (Vec v n))
      (x : denote_type t) :
  step (foldl2 (n:=n) f) tt (v1, (v2, (x, tt)))
  = (tt, List.fold_left
           (A:=denote_type t) (B:=denote_type u * denote_type v)
           (fun t uv => snd (step f tt (t,(fst uv,(snd uv,tt)))))
           (combine (List.resize default n v1)
                    (List.resize default n v2))
            x).
Proof.
  revert x; induction n; cbn [denote_type] in *; intros;
    cbn [foldl2]; stepsimpl; push_resize; push_list_fold;
      [ reflexivity | ].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite IHn. cbn [fst snd].
  rewrite !resize_succ. cbn [combine].
  push_list_fold. reflexivity.
Qed.
Hint Rewrite @step_foldl2 using solve [eauto] : stepsimpl.

Lemma step_endian_swap32 (x : denote_type (BitVec 32)) :
  step endian_swap32 tt (x, tt)
  = (tt, N.lor
          (N.land (N.shiftr x 24) (N.ones 8))
        (N.lor
          (N.land (N.shiftl x 8) (N.shiftl (N.ones 8) 16))
        (N.lor
          (N.land (N.shiftr x 8) (N.shiftl (N.ones 8) 8))
          (N.land (N.shiftl x 24) (N.shiftl (N.ones 8) 24))))).
Proof.
  cbv [endian_swap32]. stepsimpl. f_equal.
  apply N.bits_inj; intro i. push_Ntestbit.
  cbn [Nat.add].

  destr (i <? N.of_nat 8)%N;
  [|destr (i <? N.of_nat 16)%N;
  [|destr (i <? N.of_nat 24)%N;
  [|destr (i <? N.of_nat 32)%N]
  ]]; push_Ntestbit; boolsimpl.

  all: try reflexivity; f_equal; prove_by_zify.
Qed.

Hint Rewrite @step_endian_swap32 using solve [eauto] : stepsimpl.
