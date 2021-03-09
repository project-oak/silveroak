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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.List.
Require Import AesSpec.Polynomial.
Import ListNotations.
Local Open Scope list_scope.

Section PolynomialProperties.
  Context {A} {ops : FieldOperations A}.
  Context {rtheory : semi_ring_theory fzero fone fadd fmul eq}.
  Add Ring ringA : rtheory.

  Local Infix "+" := fadd.
  Local Infix "-" := fsub.
  Local Infix "*" := fmul.

  Lemma add_poly_0_l p : add_poly zero_poly p = p.
  Proof.
    cbv [add_poly zero_poly extend].
    autorewrite with push_length listsimpl natsimpl.
    induction p; intros; [ reflexivity | ].
    cbn [length repeat map2]. rewrite IHp.
    f_equal; ring.
  Qed.

  Lemma add_poly_comm p q : add_poly p q = add_poly q p.
  Proof.
    cbv [add_poly]. rewrite map2_swap.
    eapply map2_ext. intros; ring.
  Qed.

  Lemma add_poly_cons p0 q0 (p q : poly A) :
    add_poly (p0 :: p) (q0 :: q) = fadd p0 q0 :: add_poly p q.
  Proof.
    cbv [add_poly]. autorewrite with push_length.
    rewrite !extend_cons_S. reflexivity.
  Qed.

  Lemma add_poly_0_r (p : poly A) : add_poly p zero_poly = p.
  Proof. rewrite add_poly_comm; apply add_poly_0_l. Qed.

  Lemma add_poly_assoc p q r :
    add_poly p (add_poly q r) = add_poly (add_poly p q) r.
  Proof.
    revert q r; induction p; destruct q,r;
      rewrite ?add_poly_0_l, ?add_poly_0_r, ?add_poly_cons;
      try reflexivity; [ ].
    rewrite IHp. f_equal; ring.
  Qed.

  Lemma add_poly_app_zero p1 p2 :
    add_poly p1 (repeat fzero (length p1) ++ p2) = p1 ++ p2.
  Proof.
    revert p2; induction p1; intros.
    { rewrite add_poly_0_l. reflexivity. }
    { cbn [length repeat]. rewrite <-!app_comm_cons.
      rewrite add_poly_cons, IHp1. f_equal; ring. }
  Qed.

  Lemma mul_poly_1_l p : mul_poly one_poly p = p.
  Proof.
    cbv [mul_poly mul_indexed_poly mul_term one_poly]. cbn.
    autorewrite with listsimpl.
    cbv [to_indexed_poly]. rewrite map_map.
    cbv [indexed_term_to_poly].
    induction p using rev_ind; [ reflexivity | ].
    autorewrite with push_length.
    rewrite Nat.add_1_r.
    autorewrite with pull_snoc natsimpl.
    rewrite combine_append by length_hammer.
    rewrite map_app, fold_left_app.
    cbn [combine map fold_left fst snd] in *.
    rewrite IHp. rewrite add_poly_app_zero.
    repeat (f_equal; try ring).
  Qed.

  Lemma of_indexed_poly_app p1 p2 :
    of_indexed_poly (p1 ++ p2) = add_poly (of_indexed_poly p1) (of_indexed_poly p2).
  Proof.
    cbv [of_indexed_poly].
    revert p2; induction p1; intros.
    { autorewrite with listsimpl. cbn [map fold_left].
      rewrite add_poly_0_l. reflexivity. }
    { rewrite <-app_comm_cons. cbn [map fold_left].
      rewrite !add_poly_0_l.
      rewrite !fold_left_assoc with (start:=indexed_term_to_poly _)
                                    (id:=zero_poly)
        by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_0_r.
      rewrite IHp1, add_poly_assoc. reflexivity. }
  Qed.

  Lemma mul_poly_0_l p : mul_poly zero_poly p = zero_poly.
  Proof. reflexivity. Qed.

  Lemma add_poly_fzero_l n p :
    add_poly (repeat fzero n) p = p ++ repeat fzero (n - length p).
  Proof.
    revert p; induction n; destruct p; intros; autorewrite with natsimpl listsimpl;
      cbn [repeat]; rewrite ?add_poly_0_l, ?add_poly_0_r;
      [ reflexivity .. | ].
    rewrite add_poly_cons. rewrite IHn.
    autorewrite with push_length natsimpl. rewrite <-app_comm_cons.
    f_equal; ring.
  Qed.

  Lemma mul_poly_fzero_l q :
    mul_poly [fzero] q = repeat fzero (length q).
  Proof.
    cbv [mul_poly mul_indexed_poly mul_term to_indexed_poly].
    cbn [map flat_map fst snd app length seq combine].
    autorewrite with listsimpl natsimpl.
    induction q using rev_ind; [ reflexivity | ].
    autorewrite with push_length. rewrite Nat.add_1_r.
    autorewrite with pull_snoc natsimpl.
    rewrite combine_append by length_hammer.
    rewrite map_app, of_indexed_poly_app.
    rewrite IHq.
    cbn [combine of_indexed_poly fold_left map fst snd].
    rewrite add_poly_0_l. autorewrite with natsimpl.
    match goal with
      | |- context [fzero * ?x] =>
        replace (fzero * x) with fzero by ring
    end.
    cbv [indexed_term_to_poly]; cbn [fst snd].
    rewrite <-repeat_cons. rewrite add_poly_fzero_l.
    autorewrite with push_length natsimpl. cbn [repeat].
    autorewrite with listsimpl; reflexivity.
  Qed.

  Lemma add_poly_length p q : length (add_poly p q) = Nat.max (length p) (length q).
  Proof. cbv [add_poly]; length_hammer. Qed.

  Lemma mul_poly_singleton_length p0 q : length (mul_poly [p0] q) = length q.
  Proof.
    cbv [mul_poly]. change (to_indexed_poly [p0]) with [(0%nat, p0)].
    cbv [mul_indexed_poly mul_term]. cbn [flat_map fst snd]. autorewrite with listsimpl.
    cbv [to_indexed_poly of_indexed_poly].
    induction q using rev_ind; intros; [ reflexivity | ].
    autorewrite with push_length. rewrite Nat.add_1_r.
    autorewrite with pull_snoc. rewrite !combine_append by length_hammer.
    rewrite !map_app. rewrite fold_left_app.
    cbn [combine map fst snd fold_left]. autorewrite with natsimpl.
    autorewrite with push_length. rewrite add_poly_length, IHq.
    cbv [indexed_term_to_poly]. autorewrite with push_length. cbn [fst].
    lia.
  Qed.

  Lemma mul_indexed_poly_cons_l p0 p q :
    of_indexed_poly (mul_indexed_poly (p0 :: p) q)
    = add_poly (of_indexed_poly (mul_term p0 q))
               (of_indexed_poly (mul_indexed_poly p q)).
  Proof.
    cbv [of_indexed_poly mul_indexed_poly].
    cbn [flat_map]. rewrite map_app, fold_left_app.
    rewrite fold_left_assoc with (start:=fold_left _ _ _) (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_0_r.
    reflexivity.
  Qed.

  Lemma of_indexed_poly_cons p0 p :
    of_indexed_poly (p0 :: p) = add_poly (indexed_term_to_poly p0) (of_indexed_poly p).
  Proof.
    cbv [of_indexed_poly]. cbn [map fold_left]. rewrite add_poly_0_l.
    apply fold_left_assoc;
      auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_0_r.
  Qed.

  Lemma mul_term_cons t p0 p :
    mul_term t (p0 :: p) = ((fst t + fst p0)%nat, snd t * snd p0) :: mul_term t p.
  Proof. reflexivity. Qed.

  (* This pattern comes up quite a bit in later lemmas *)
  Lemma add_poly_arith_helper a b c d :
    add_poly (add_poly a b) (add_poly c d)
    = add_poly (add_poly a c) (add_poly b d).
  Proof.
    rewrite (add_poly_assoc (add_poly a c) b d).
    rewrite (add_poly_comm (add_poly a c) b).
    rewrite (add_poly_assoc b a c).
    rewrite <-(add_poly_assoc (add_poly b a) c d).
    rewrite (add_poly_comm b a).
    reflexivity.
  Qed.

  Lemma mul_indexed_poly_cons_r p q0 q :
    of_indexed_poly (mul_indexed_poly p (q0 :: q))
    = add_poly (of_indexed_poly (mul_term q0 p))
               (of_indexed_poly (mul_indexed_poly p q)).
  Proof.
    cbv [mul_indexed_poly].
    induction p as [|p0 p]; [ reflexivity | ].
    cbn [flat_map]. rewrite !of_indexed_poly_app, !mul_term_cons.
    rewrite !of_indexed_poly_cons. rewrite IHp.
    (* commutativity for very first terms *)
    rewrite (Nat.add_comm (fst q0) (fst p0)).
    replace (snd q0 * snd p0) with (snd p0 * snd q0) by ring.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_indexed_poly_cons p0 p q0 q :
    of_indexed_poly (mul_indexed_poly (p0 :: p) (q0 :: q)) =
    add_poly (add_poly (indexed_term_to_poly ((fst p0 + fst q0)%nat, snd p0 * snd q0))
                       (of_indexed_poly (mul_term p0 q)))
             (add_poly (of_indexed_poly (mul_term q0 p))
                       (of_indexed_poly (mul_indexed_poly p q))).
  Proof.
    rewrite !mul_indexed_poly_cons_l. rewrite !mul_term_cons.
    rewrite !mul_indexed_poly_cons_r. rewrite !of_indexed_poly_cons.
    reflexivity.
  Qed.

  Lemma mul_indexed_poly_comm p q :
    of_indexed_poly (mul_indexed_poly p q) = of_indexed_poly (mul_indexed_poly q p).
  Proof.
    revert q; induction p as [|p0 p]; destruct q as [|q0 q]; intros;
      [ cbn [of_indexed_poly mul_indexed_poly mul_term map flat_map app fold_left];
        rewrite ?flat_map_nil_ext; reflexivity .. | ].
    rewrite !mul_indexed_poly_cons.
    (* commutativity for very first terms *)
    rewrite (Nat.add_comm (fst q0) (fst p0)).
    replace (snd q0 * snd p0) with (snd p0 * snd q0) by ring.
    rewrite IHp. apply add_poly_arith_helper.
  Qed.

  Lemma mul_poly_comm p q : mul_poly p q = mul_poly q p.
  Proof.
    cbv [mul_poly]. rewrite mul_indexed_poly_comm. reflexivity.
  Qed.

  Lemma mul_term_mul_indexed_poly_l t p q :
    of_indexed_poly (mul_term t (mul_indexed_poly p q))
    = of_indexed_poly (mul_indexed_poly (mul_term t p) q).
  Proof.
    cbv [of_indexed_poly mul_term mul_indexed_poly].
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    cbn [flat_map map]. rewrite !map_app, !fold_left_app.
    cbn [fst snd].
    rewrite !fold_left_assoc with (start:=fold_left _ _ _)
                                  (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_0_r.
    rewrite IHp. f_equal; [ ].
    rewrite !map_map. cbn [fst snd].
    f_equal; [ ]. apply map_ext; intros.
    repeat (f_equal; try lia; try ring).
  Qed.

  Lemma mul_term_mul_indexed_poly_r t p q :
    of_indexed_poly (mul_term t (mul_indexed_poly p q))
    = of_indexed_poly (mul_indexed_poly p (mul_term t q)).
  Proof.
    cbv [of_indexed_poly mul_term mul_indexed_poly].
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    cbn [flat_map map]. rewrite !map_app, !fold_left_app.
    cbn [fst snd].
    rewrite !fold_left_assoc with (start:=fold_left _ _ _)
                                  (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_0_r.
    rewrite IHp. f_equal; [ ].
    rewrite !map_map. cbn [fst snd].
    f_equal; [ ]. apply map_ext; intros.
    repeat (f_equal; try lia; try ring).
  Qed.

  Lemma mul_term_shift_l i x p : mul_term (S i, x) p = map (fun t => (S (fst t), snd t))
                                                         (mul_term (i,x) p).
  Proof.
    cbv [mul_term]. rewrite map_map. cbn [fst snd]. reflexivity.
  Qed.

  Lemma mul_term_shift_r t p :
    mul_term t (map (fun t => (S (fst t), snd t)) p)
    = map (fun t => (S (fst t), snd t)) (mul_term t p).
  Proof.
    cbv [mul_term]. rewrite !map_map. cbn [fst snd].
    apply map_ext; intros; f_equal; lia.
  Qed.

  Lemma cons_fzero_distr_l p q :
    fzero :: add_poly p q = add_poly (fzero :: p) (fzero :: q).
  Proof.
    cbv [add_poly]. autorewrite with push_length.
    rewrite !extend_cons_S. cbn [map2]. f_equal; ring.
  Qed.

  Lemma to_indexed_poly_cons p0 (p : poly A) :
    to_indexed_poly (p0 :: p) = (0%nat, p0) :: map (fun t => (S (fst t), snd t)) (to_indexed_poly p).
  Proof.
    cbv [to_indexed_poly]. cbn [length seq combine].
    erewrite <-seq_shift. rewrite combine_map_l.
    reflexivity.
  Qed.

  Definition shift_poly (p : poly A) : poly A :=
    match p with
    | [] => []
    | _ => fzero :: p
    end.

  Lemma indexed_term_to_poly_shift_poly n x :
    indexed_term_to_poly (S n, x) = shift_poly (indexed_term_to_poly (n, x)).
  Proof.
    cbv [indexed_term_to_poly shift_poly]. cbn [fst snd repeat].
    destruct n; cbn [repeat]; [ reflexivity | ].
    rewrite <-!app_comm_cons. reflexivity.
  Qed.

  Lemma add_poly_shift_poly p q :
    add_poly (shift_poly p) (shift_poly q) = shift_poly (add_poly p q).
  Proof.
    destruct p, q; cbn [shift_poly];
      rewrite ?add_poly_0_l, ?add_poly_0_r; [ reflexivity .. | ].
    rewrite !add_poly_cons. cbn [shift_poly].
    f_equal; ring.
  Qed.

  Lemma of_indexed_poly_shift p :
    of_indexed_poly (map (fun t => (S (fst t), snd t)) p) = shift_poly (of_indexed_poly p).
  Proof.
    induction p as [|p0 p]; cbn [map]; [ reflexivity | ].
    rewrite !of_indexed_poly_cons, IHp.
    rewrite indexed_term_to_poly_shift_poly, add_poly_shift_poly.
    destruct p0; reflexivity.
  Qed.

  Lemma mul_poly_cons_l p0 (p q : poly A) :
    mul_poly (p0 :: p) q = add_poly (of_indexed_poly (mul_term (0%nat, p0) (to_indexed_poly q)))
                                   (shift_poly (mul_poly p q)).
  Proof.
    intros; cbv [mul_poly]. rewrite to_indexed_poly_cons.
    rewrite mul_indexed_poly_cons_l.
    f_equal; [ ]. cbv [mul_indexed_poly].
    rewrite flat_map_map.
    erewrite flat_map_ext by (intros; apply mul_term_shift_l).
    rewrite <-map_flat_map. rewrite of_indexed_poly_shift.
    reflexivity.
  Qed.

  Lemma add_poly_snoc n x y :
    add_poly (repeat fzero n ++ [x]) (repeat fzero n ++ [y]) = repeat fzero n ++ [x + y].
  Proof.
    cbv [add_poly]. rewrite !extend_le by length_hammer.
    induction n; [ reflexivity | ].
    cbn [repeat]. rewrite <-!app_comm_cons. cbn [map2].
    rewrite IHn. f_equal; ring.
  Qed.

  Lemma mul_term_distr_l x y p :
    of_indexed_poly (mul_term (0%nat, x + y) p) = add_poly (of_indexed_poly (mul_term (0%nat, x) p))
                                                         (of_indexed_poly (mul_term (0%nat, y) p)).
  Proof.
    cbv [mul_term]. cbn [fst snd].
    induction p as [|p0 p]; [ reflexivity | ].
    cbn [map]. rewrite !of_indexed_poly_cons.
    rewrite IHp. cbv [indexed_term_to_poly]. cbn [fst snd].
    replace ((x + y) * snd p0) with (x * snd p0 + y * snd p0) by ring.
    rewrite <-add_poly_snoc.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_poly_singleton x (p : poly A) :
    mul_poly [x] p = of_indexed_poly (mul_term (0%nat, x) (to_indexed_poly p)).
  Proof.
    cbv [mul_poly mul_indexed_poly].
    cbn [to_indexed_poly length seq combine map flat_map].
    autorewrite with listsimpl. reflexivity.
  Qed.

  Lemma mul_term_mul_term t1 t2 p :
    mul_term t1 (mul_term t2 p) = mul_term ((fst t1 + fst t2)%nat, snd t1 * snd t2) p.
  Proof.
    cbv [mul_term]. rewrite !map_map; cbn [fst snd].
    apply map_ext; intros; f_equal; lia || ring.
  Qed.

  Lemma indexed_term_to_poly_add_r i x y :
    indexed_term_to_poly (i, x + y) = add_poly (indexed_term_to_poly (i,x))
                                               (indexed_term_to_poly (i,y)).
  Proof.
    cbv [indexed_term_to_poly add_poly]. cbn [fst snd].
    rewrite !extend_le, map2_app by length_hammer.
    rewrite map2_drop_same, map_repeat by auto.
    cbn [map2]. repeat (f_equal; try ring).
  Qed.

  Lemma mul_term_distr_r t p q :
    of_indexed_poly
      (mul_term t (to_indexed_poly (add_poly p q)))
    = add_poly (of_indexed_poly (mul_term t (to_indexed_poly p)))
               (of_indexed_poly (mul_term t (to_indexed_poly q))).
  Proof.
    revert t q; induction p; destruct q; intros;
      [ rewrite ?add_poly_0_l, ?add_poly_0_r; reflexivity .. | ].
    rewrite add_poly_cons, !to_indexed_poly_cons, !mul_term_cons.
    rewrite !of_indexed_poly_cons. cbn [fst snd].
    rewrite !mul_term_shift_r, !of_indexed_poly_shift.
    rewrite IHp. rewrite <-add_poly_shift_poly.
    match goal with
    | |- context [ ?a * (?b + ?c) ] =>
      replace (a * (b + c)) with (a * b + a * c) by ring
    end.
    rewrite indexed_term_to_poly_add_r.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_indexed_poly_distr_r p q r :
    of_indexed_poly
      (mul_indexed_poly p (to_indexed_poly (add_poly q r))) =
    add_poly
      (of_indexed_poly (mul_indexed_poly p (to_indexed_poly q)))
      (of_indexed_poly (mul_indexed_poly p (to_indexed_poly r))).
  Proof.
    revert q r; induction p as [|p0 p]; intros; [ reflexivity | ].
    rewrite !mul_indexed_poly_cons_l. rewrite IHp.
    rewrite mul_term_distr_r. apply add_poly_arith_helper.
  Qed.

  Lemma mul_poly_distr_l p q r :
    mul_poly (add_poly p q) r = add_poly (mul_poly p r) (mul_poly q r).
  Proof.
    rewrite !(mul_poly_comm _ r).
    revert p q; induction r as [|r0 r]; intros;
      [ rewrite !mul_poly_0_l; reflexivity .. | ].
    rewrite !mul_poly_cons_l.
    rewrite mul_term_distr_r. rewrite IHr.
    rewrite <-add_poly_shift_poly.
    apply add_poly_arith_helper.
  Qed.

  Lemma shift_poly_length p :
    p <> nil -> length (shift_poly p) = S (length p).
  Proof. destruct p; [ congruence | ]; cbn [shift_poly]; length_hammer. Qed.

  Lemma shift_poly_length_le p : (length p <= length (shift_poly p))%nat.
  Proof. destruct p; cbn [shift_poly]; length_hammer. Qed.

  Lemma mul_poly_shift_l p q :
    mul_poly (shift_poly p) q = shift_poly (mul_poly p q).
  Proof.
    destruct p; [ reflexivity | ].
    cbn [shift_poly]. rewrite !mul_poly_cons_l.
    rewrite <-!mul_poly_singleton.
    rewrite mul_poly_fzero_l, add_poly_fzero_l.
    rewrite (proj2 (Nat.sub_0_le _ _));
      [ cbn [repeat]; autorewrite with listsimpl; reflexivity | ].
    rewrite <-!add_poly_shift_poly.
    rewrite add_poly_length.
    match goal with |- context [length (shift_poly (mul_poly [?x] ?p))] =>
                    pose proof (shift_poly_length_le (mul_poly [x] p))
    end.
    rewrite !mul_poly_singleton_length in *.
    lia.
  Qed.

  Lemma of_indexed_poly_to_indexed_poly p :
    of_indexed_poly (to_indexed_poly p) = p.
  Proof.
    induction p; [ reflexivity | ].
    rewrite !to_indexed_poly_cons, of_indexed_poly_cons.
    rewrite of_indexed_poly_shift. rewrite IHp.
    cbn [indexed_term_to_poly fst snd repeat app].
    destruct p; [ cbn; f_equal; ring | ].
    cbn [shift_poly].
    rewrite add_poly_cons, add_poly_0_l.
    f_equal; ring.
  Qed.

  Lemma add_poly_singleton_shift x p :
    add_poly (indexed_term_to_poly (0, x)) (shift_poly p) = x :: p.
  Proof.
    cbn [indexed_term_to_poly fst snd repeat app].
    destruct p; [ cbn; f_equal; ring | ].
    cbv [add_poly shift_poly]. cbn [length].
    rewrite extend_le with (l:=_ :: _ :: _) by length_hammer.
    rewrite !extend_cons_S, !extend_nil.
    cbn [repeat map2]. repeat (f_equal; [ ring | ]).
    induction p; [reflexivity | ].
    cbn [repeat map2 length]. rewrite IHp. f_equal; ring.
  Qed.

  Lemma mul_poly_singleton_map p0 (q : poly A) :
    mul_poly [p0] q = map (fmul p0) q.
  Proof.
    rewrite mul_poly_singleton.
    induction q; [ reflexivity | ].
    rewrite to_indexed_poly_cons.
    rewrite mul_term_cons; cbn [fst snd map].
    rewrite of_indexed_poly_cons.
    rewrite mul_term_shift_r, of_indexed_poly_shift.
    rewrite IHq. autorewrite with natsimpl.
    rewrite add_poly_singleton_shift. reflexivity.
  Qed.

  Lemma mul_term_mul_singleton x p0 q :
    of_indexed_poly (mul_term x (to_indexed_poly (mul_poly [p0] q)))
    = of_indexed_poly (mul_term (fst x, snd x * p0) (to_indexed_poly q)).
  Proof.
    rewrite mul_poly_singleton_map.
    cbv [to_indexed_poly]. rewrite combine_map_r.
    cbv [mul_term]. rewrite map_map.
    autorewrite with push_length.
    f_equal; apply map_ext; intros.
    cbn [fst snd].
    f_equal; ring.
  Qed.

  Lemma indexed_term_to_poly_fzero i :
    indexed_term_to_poly (i, fzero) = repeat fzero (S i).
  Proof.
    cbv [indexed_term_to_poly]. cbn [fst snd].
    rewrite <-repeat_cons. reflexivity.
  Qed.

  Lemma add_poly_indexed_term_to_poly_fzero_l i p :
    add_poly (indexed_term_to_poly (i, fzero)) p = p ++ repeat fzero (S i - length p).
  Proof.
    rewrite indexed_term_to_poly_fzero.
    rewrite add_poly_fzero_l; reflexivity.
  Qed.

  Lemma mul_term_shift_poly x p :
    of_indexed_poly (mul_term x (to_indexed_poly (shift_poly p)))
    = shift_poly (of_indexed_poly (mul_term x (to_indexed_poly p))).
  Proof.
    destruct p as [|p0 p]; [ reflexivity | ]. cbn [shift_poly].
    rewrite !to_indexed_poly_cons. cbn [map].
    rewrite !mul_term_cons. cbn [fst snd].
    rewrite !of_indexed_poly_cons.
    rewrite <-add_poly_shift_poly.
    rewrite !mul_term_shift_r, of_indexed_poly_shift.
    rewrite add_poly_assoc. f_equal; [ ].
    rewrite Nat.add_1_r.
    rewrite indexed_term_to_poly_shift_poly.
    replace (snd x * fzero) with fzero by ring.
    rewrite add_poly_indexed_term_to_poly_fzero_l.
    autorewrite with natsimpl.
    rewrite (proj2 (Nat.sub_0_le _ _));
      [ cbn [repeat]; autorewrite with listsimpl; reflexivity | ].
    cbv [indexed_term_to_poly]. cbn [fst snd].
    match goal with
    | |- context [length (shift_poly ?p)] =>
      pose proof (shift_poly_length_le p)
    end.
    autorewrite with push_length in *. lia.
  Qed.

  Lemma mul_poly_indexed_term_to_poly t p :
    mul_poly (indexed_term_to_poly t) p = of_indexed_poly (mul_term t (to_indexed_poly p)).
  Proof.
    cbv [indexed_term_to_poly]. destruct t as [i x]. cbn [fst snd].
    revert x p; induction i; intros; cbn [repeat app];
      [ solve [apply mul_poly_singleton] | ].
    rewrite mul_term_shift_l, of_indexed_poly_shift.
    rewrite <-IHi, <-mul_poly_shift_l.
    cbv [shift_poly]. destruct i; reflexivity.
  Qed.

  Lemma mul_term_mul_poly_assoc x p q :
    of_indexed_poly (mul_term x (to_indexed_poly (mul_poly p q)))
    = mul_poly (of_indexed_poly (mul_term x (to_indexed_poly p))) q.
  Proof.
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    rewrite !mul_poly_cons_l. rewrite mul_term_distr_r.
    rewrite to_indexed_poly_cons, mul_term_cons.
    cbn [fst snd]. rewrite of_indexed_poly_cons.
    rewrite <-mul_poly_singleton, mul_term_mul_singleton.
    rewrite mul_term_shift_r, of_indexed_poly_shift.
    rewrite mul_poly_distr_l, mul_poly_indexed_term_to_poly.
    autorewrite with natsimpl. f_equal; [ ].
    rewrite mul_poly_shift_l. rewrite <-IHp.
    rewrite mul_term_shift_poly.
    reflexivity.
  Qed.

  Lemma mul_poly_assoc p q r : mul_poly p (mul_poly q r) = mul_poly (mul_poly p q) r.
  Proof.
    revert q r; induction p; intros; [ reflexivity | ].
    rewrite !mul_poly_cons_l. rewrite IHp.
    rewrite mul_poly_distr_l. rewrite mul_term_mul_poly_assoc.
    rewrite mul_poly_shift_l.
    reflexivity.
  Qed.

  Lemma of_indexed_poly_length p :
    length (of_indexed_poly p) = fold_left Nat.max (map (fun t => S (fst t)) p) 0%nat.
  Proof.
    cbv [of_indexed_poly]. change 0%nat with (length (@zero_poly A)).
    generalize (@zero_poly A) as acc.
    induction p; intros; [ reflexivity | ].
    cbn [map fold_left]. rewrite IHp.
    rewrite add_poly_length.
    cbv [indexed_term_to_poly].
    autorewrite with push_length.
    rewrite Nat.add_1_r; reflexivity.
  Qed.

  Definition PolyTheory
    : semi_ring_theory zero_poly one_poly add_poly mul_poly eq.
  Proof.
    constructor.
    { apply add_poly_0_l. }
    { apply add_poly_comm. }
    { apply add_poly_assoc. }
    { apply mul_poly_1_l. }
    { apply mul_poly_0_l. }
    { apply mul_poly_comm. }
    { apply mul_poly_assoc. }
    { apply mul_poly_distr_l. }
  Qed.

  Lemma modulo_poly_small p q :
    (length p < length (remove_leading_zeroes q))%nat ->
    modulo_poly p q = p.
  Proof.
    cbv [modulo_poly div_rem_poly]. intro Hlt.
    destruct p; [ reflexivity | ].
    rewrite removelast_firstn_len.
    cbn [length div_rem_poly'].
    autorewrite with push_length in Hlt |- *.
    destruct_one_match; [ reflexivity | exfalso; lia ].
  Qed.

  Lemma mul_term_length t p :
    p <> nil ->
    length (of_indexed_poly (mul_term t (to_indexed_poly p)))
    = (fst t + length p)%nat.
  Proof.
    intros; cbv [mul_term to_indexed_poly].
    rewrite of_indexed_poly_length.
    rewrite map_map. cbn [fst snd].
    induction p using rev_ind; [ congruence | ].
    destruct p as [|p1 p']; [ cbn; lia | set (p:=p1 :: p') in * ].
    autorewrite with push_length.
    rewrite Nat.add_1_r.
    autorewrite with pull_snoc natsimpl.
    rewrite combine_append by length_hammer.
    rewrite map_app. cbn [map combine fst snd].
    rewrite fold_left_app.
    rewrite IHp by (subst p; congruence).
    cbn; lia.
  Qed.

  Lemma mul_poly_nonnil (p q : poly A) :
    p <> nil -> q <> nil -> mul_poly p q <> nil.
  Proof.
    revert q. induction p as [|p0 p]; intros; [ congruence | ].
    destruct p as [|p1 p']; [ | set (p:=p1 :: p') in * ];
      [ apply length_pos_nonnil; rewrite mul_poly_singleton_length;
        destruct q; [ congruence | ]; length_hammer | ].
    apply length_pos_nonnil.
    rewrite mul_poly_cons_l, add_poly_length.
    rewrite mul_term_length by auto. cbn [fst snd].
    rewrite shift_poly_length; [ lia | ].
    apply IHp; subst p; congruence.
  Qed.

  Lemma mul_poly_length (p q : poly A) :
    p <> nil -> q <> nil ->
    length (mul_poly p q) = (length p + length q - 1)%nat.
  Proof.
    revert q. induction p as [|p0 p]; intros; [ congruence | ].
    destruct p as [|p1 p']; [ | set (p:=p1 :: p') in * ];
      [ rewrite mul_poly_singleton_length;
        destruct q; [ congruence | ]; length_hammer | ].
    cbn [length]. rewrite mul_poly_cons_l, add_poly_length.
    rewrite mul_term_length by auto. cbn [fst snd].
    rewrite shift_poly_length by (apply mul_poly_nonnil; subst p; congruence).
    rewrite IHp by (subst p; congruence).
    autorewrite with natsimpl.
    subst p; length_hammer.
  Qed.
End PolynomialProperties.
