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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Sha256.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.NPushPullMod.
Require HmacSpec.SHA256.
Import ListNotations.

(* TODO: move to a more general file *)
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
                   cbn [fst snd step denote_type absorb_any
                            split_absorbed_denotation combine_absorbed_denotation
                            unary_semantics binary_semantics eqb ]
               | progress autorewrite with stepsimpl ].

(* TODO: move to a more general file *)
Lemma step_index {t n i} (x : denote_type (Vec t n))
      (idx : denote_type (BitVec i)) :
  step (@index _ t n i) tt (x, (idx, tt))
  = (tt, nth (N.to_nat idx) (List.resize default n x) default).
Proof. reflexivity. Qed.
Hint Rewrite @step_index using solve [eauto] : stepsimpl.

Lemma resize_0 {A} (d : A) ls : List.resize d 0 ls = [].
Proof.
  cbv [List.resize]. autorewrite with push_firstn natsimpl. reflexivity.
Qed.
Lemma resize_succ {A} (d : A) n ls :
  List.resize d (S n) ls = hd d ls :: List.resize d n (tl ls).
Proof.
  cbv [List.resize].
  destruct ls; autorewrite with push_firstn natsimpl; reflexivity.
Qed.

(* TODO: move to a more general file *)
Lemma step_uncons {t n}  (x : denote_type [Vec t (S n)]) :
  step (@uncons _ t n) tt x = (tt, (hd default (fst x), tl (fst x))).
Proof. destruct x; reflexivity. Qed.
Hint Rewrite @step_uncons using solve [eauto] : stepsimpl.

(* TODO: move to a more general file *)
Lemma step_stateless {i o} (f : Circuit [] i o) (x : denote_type i) :
  step f tt x = (tt, snd (step f tt x)).
Proof.
  rewrite (surjective_pairing (step f tt x)).
  destruct (fst (step f tt x)). reflexivity.
Qed.

(* TODO: move to a more general file *)
Lemma step_map2 {t u v n} (f : Circuit [] [t;u] v)
      (x : denote_type [Vec t n; Vec u n]) :
  step (@Expr.map2 _ t u v n f) tt x
  = (tt, map2 (fun (x1 : denote_type t) (x2 : denote_type u) =>
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

Lemma step_rotr n (x : denote_type sha_word) :
  step (rotr n) tt (x,tt) = (tt, SHA256.ROTR (N.of_nat n) x).
Proof.
  cbv [rotr]. stepsimpl.
  cbv [SHA256.ROTR SHA256.truncating_shiftl SHA256.w].
  repeat (f_equal; try lia).
Qed.
Hint Rewrite @step_rotr using solve [eauto] : stepsimpl.

(* TODO: move *)
Lemma resize_length {A} (d : A) n ls : length (List.resize d n ls) = n.
Proof. cbv [List.resize]. length_hammer. Qed.
Hint Rewrite @resize_length using solve [eauto] : push_length.

(* TODO: move *)
Lemma firstn_map_nth {A} (d : A) n ls :
  n <= length ls -> firstn n ls = List.map (fun i : nat => nth i ls d) (seq 0 n).
Proof.
  revert ls; induction n; [ reflexivity | ].
  intros. erewrite firstn_succ_snoc by lia. rewrite IHn by lia.
  autorewrite with pull_snoc. reflexivity.
Qed.

(* TODO: move *)
Lemma resize_map_nth {A} (d : A) n ls :
  List.resize d n ls = List.map (fun i => nth i ls d) (seq 0 n).
Proof.
  intros; subst. cbv [List.resize].
  destr (n <=? length ls);
    autorewrite with natsimpl listsimpl push_firstn;
    [ solve [auto using firstn_map_nth] | ].
  replace n with (length ls + (n - length ls)) by lia.
  rewrite seq_app, map_app, <-firstn_map_nth by lia.
  autorewrite with natsimpl push_firstn. apply f_equal.
  erewrite map_ext_in; [ rewrite map_constant; f_equal; length_hammer | ].
  intros *. rewrite in_seq. intros.
  rewrite nth_overflow by lia; reflexivity.
Qed.

Lemma hd_to_nth {A} (d : A) ls : hd d ls = nth 0 ls d.
Proof. destruct ls; reflexivity. Qed.
Hint Rewrite @hd_to_nth @nth_tl using solve [eauto] : hd_tl_to_nth.

Lemma step_sha256_compress
      (H : denote_type sha_digest)
      (k w : denote_type sha_word) (t i : nat) (msg : list byte) :
  k = nth t SHA256.K 0%N ->
  w = nth t (SHA256.W msg i) 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress msg i (List.resize 0%N 8 H) t).
Proof.
  intros. rewrite resize_map_nth. cbn [List.map seq].
  subst. cbv [sha256_compress]. stepsimpl.
  autorewrite with hd_tl_to_nth.
  reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.


(* TODO: move to Spec.SHA256Properties *)
Lemma nth_W msg (i t : nat) :
  (t < 64) ->
  nth t (SHA256.W msg i) 0%N =
  if (t <? 16)%nat
  then SHA256.M msg t i
  else
    let W_tm2 := nth (t - 2) (SHA256.W msg i) 0%N in
    let W_tm7 := nth (t - 7) (SHA256.W msg i) 0%N in
    let W_tm15 := nth (t - 15) (SHA256.W msg i) 0%N in
    let W_tm16 := nth (t - 16) (SHA256.W msg i) 0%N in
    SHA256.add_mod
      (SHA256.add_mod
         (SHA256.add_mod
            (SHA256.sigma1 W_tm2) W_tm7) (SHA256.sigma0 W_tm15))
      W_tm16.
Proof.
  intros.
  (* extract the formula for an element of W and remember it *)
  lazymatch goal with
    | |- nth t ?W ?d = ?rhs =>
      let f := lazymatch (eval pattern t in rhs) with
               | ?f _ => f end in
      let f := lazymatch (eval pattern W in f) with
               | ?f _ => f end in
      set (W_formula:=f);
        change (nth t W d = W_formula W t)
  end.
  (* use an invariant *)
  apply fold_left_invariant_seq
    with (I:= fun n W =>
                length W = n /\
                forall t, t < n -> nth t W 0%N = W_formula W t)
         (P:=fun W => nth t W 0%N = W_formula W t);
    [ intros; ssplit; length_hammer
    | | intros; ssplit; logical_simplify; solve [auto] ].
  intros. autorewrite with natsimpl push_nth in *.
  logical_simplify. ssplit; [ length_hammer | ]. intros.
  lazymatch goal with H : ?t < S ?n |- context [nth ?t] =>
                      destr (t <? n); [ | replace t with n in * by lia ]
  end; subst W_formula; cbn beta; autorewrite with natsimpl push_nth;
    [ solve [auto] | ].
  destruct_one_match; autorewrite with push_nth; reflexivity.
Qed.

Lemma step_sha256_message_schedule_update
      (w0 w1 w9 w14 : denote_type sha_word) (t i : nat) msg :
  w0 = nth (t-16) (SHA256.W msg i) 0%N ->
  w1 = nth (t-15) (SHA256.W msg i) 0%N ->
  w9 = nth (t-7) (SHA256.W msg i) 0%N ->
  w14 = nth (t-2) (SHA256.W msg i) 0%N ->
  (16 <= t < 64) ->
  step sha256_message_schedule_update tt (w0, (w1, (w9, (w14, tt))))
  = (tt, nth t (SHA256.W msg i) 0%N).
Proof.
  intros. cbv [sha256_message_schedule_update]. stepsimpl.
  rewrite nth_W by lia. destruct_one_match; [ lia | ].
  repeat match goal with H : _ = nth ?n _ _ |- _ =>
                         rewrite <-H end.
  cbv [SHA256.add_mod SHA256.w]. N.push_pull_mod.
  cbv [SHA256.sigma1 SHA256.sigma0 SHA256.SHR].
  cbn [N.of_nat Pos.of_succ_nat Pos.succ].
  repeat (f_equal; try lia).
Qed.
Hint Rewrite @step_sha256_message_schedule_update using solve [eauto] : stepsimpl.

(* TODO: move *)
Lemma resize_noop {A} (d : A) n ls :
  n = length ls -> List.resize d n ls = ls.
Proof.
  intros; subst. cbv [List.resize].
  autorewrite with natsimpl listsimpl push_firstn.
  reflexivity.
Qed.

Lemma step_sha256_round_constants (round : denote_type sha_round) :
  step sha256_round_constants tt (round, tt)
  = (tt, nth (N.to_nat round) SHA256.K 0%N).
Proof. reflexivity. Qed.
Hint Rewrite @step_sha256_round_constants using solve [eauto] : stepsimpl.

(* TODO: move *)
Module List.
  Definition slice {A} (d : A) ls start len : list A :=
    List.resize d len (skipn start ls).
End List.

(*
  (* SHA-256 inner core *)
  (* `initial_digest` must be held until done *)
  Definition sha256_inner : Circuit _ [Bit; sha_block; sha_digest; Bit] (sha_digest ** Bit) :=
    {{
    fun block_valid block initial_digest clear =>

    let/delay '(current_digest, message_schedule, done; round) :=

      let inc_round := !done in
      let start := (* done && *) block_valid in

      let k_i := `sha256_round_constants` round in
      let '(w0,w1, _, _, _, _, _, _
           , _,w9, _, _, _, _,w14;_ ) := `vec_as_tuple (n:=15)` message_schedule in
      let update_schedule := round >= `K 15` in
      let w16 :=
        if update_schedule
        then `sha256_message_schedule_update` w0 w1 w9 w14
        else `index` message_schedule round in
      let w :=
        if update_schedule
        then message_schedule <<+ w16
        else message_schedule in

      let next_digest := `sha256_compress` current_digest k_i
        (`index` message_schedule (
          if round >= `K 16`
          then `K 15`
          else round)
        ) in

      let done := (round == `K 64`) | done in
      let round := if inc_round then round + `K 1` else round in

      if start | clear
      then (initial_digest, block, `Constant (Bit**sha_round) (0, 0)`)
      else if done then (current_digest, message_schedule, done, round)
      else (next_digest, w, done, round)

      initially (((sha256_initial_digest, (repeat 0 16, (1, 0))))
      : denote_type (sha_digest ** sha_block ** Bit ** sha_round )) in

    let updated_digest := `map2 {{fun a b => ( a + b ) }}` initial_digest current_digest in
    (updated_digest, done)

  }}.
 *)

(*
  if block_valid OR clear is true:
     new_state := (initial_digest, block, 0, 0)
     out := (map2 add initial_digest initial_digest, 0)
  otherwise:
     if done is false:
        new_round := round + 1
     if done is true OR round = 64:
        new_done := true
        new_state := (current_digest, message_schedule, 1, new_round)
        out := (map2 add initial_digest current_digest, 1)
     otherwise:
        if round >= 15:
           next_digest := compress current_digest k[round] message_schedule[15]
           new_state := (next_digest, updated message schedule, 0, new_round)
           out := (map2 add initial_digest next_digest, 0)
        otherwise:
           next_digest := compress current_digest k[round] message_schedule[round]
           new_state := (next_digest, message_schedule, 0, new_round)
           out := (map2 add initial_digest next_digest, 0)

 *)
Print SHA256.sha256.
Definition sha256_inner_invariant
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (H : list N) (i : nat) : Prop :=
  let '(current_digest, (message_schedule, (done, round))) := state in
  (* either we're done *)
  (done = 1%N)
  (* ...or we're not done *)
  \/ (done = 0%N
     (* ...and the round is < 64 *)
     /\ (round < 64)%N
     (* ...and the message schedule is the expected slice of the message *)
     /\ message_schedule = List.slice 0%N (SHA256.W msg i) (N.to_nat round - 15) 16
     (* ...and the current digest is the expected digest *)
     /\ current_digest = fold_left (SHA256.sha256_compress msg i)
                                  (seq 0 (N.to_nat round)) H).

Definition sha256_inner_pre
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           msg (i : nat) : Prop :=
  let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
  (* either clear is true, and the message ghost variable is empty *)
  ((clear = 1%N /\ msg = repeat x00 16 /\ i = 0%nat)
     (* or clear is false *)
     \/ (clear = 0%N))
  (* ...and the initial digest is the digest from the previous i *)
  /\ initial_digest = fold_left (SHA256.sha256_step msg) (seq 0 i) SHA256.H0
  (* ...and either the block is valid *)
  /\ ((block_valid = 1%N
      (* ...and the block is the expected slice of the message *)
      /\ block = List.slice 0%N (SHA256.W msg i) 0 16)
     (* ...or the block is not valid *)
     \/ (block_valid = 0%N)).

Definition sha256_inner_spec
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (i : nat) : denote_type (sha_digest ** Bit) :=
  let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
  let '(current_digest, (message_schedule, (done, round))) := state in
  let next_digest := if (clear =? 1)%N
                     then SHA256.H0
                     else if (block_valid =? 1)%N
                          then initial_digest
                          else if (done =? 0)%N
                               then SHA256.sha256_compress
                                      msg i (List.resize 0%N 8 current_digest)
                                      (N.to_nat round)
                               else current_digest in
  let next_done := if (clear =? 1)%N
                   then 1%N
                   else if (block_valid =? 1)%N
                        then 0%N
                        else if (done =? 0)%N
                             then (if (round =? 63) then 1 else 0)%N
                             else 1%N in
  (map2 SHA256.add_mod (List.resize 0%N 8 initial_digest)
        (List.resize 0%N 8 next_digest), next_done).

(*
Definition sha256_inner_spec
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (i : nat)
  : denote_type (sha_digest ** sha_block ** Bit ** sha_round)
    * denote_type (sha_digest ** Bit) :=
  let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
  let '(current_digest, (message_schedule, (done, round))) := state in
  let add_to_initial := map2 SHA256.add_mod (List.resize 0%N 8 initial_digest) in
  if negb (N.lor block_valid clear =? 0)%N
  then
    (* return dummy values *)
    let new_state := (initial_digest, (block, (0%N, 0%N))) in
    let out := (add_to_initial initial_digest, 0%N) in
    (new_state, out)
  else
    let new_round := (if (N.lnot done 1 =? 0)%N then round + 1 else round)%N in
    if (negb (done =? 0)%N || (round =? 64)%N)%bool
    then
      (* computation done; hold current values *)
      let new_state := (current_digest, (message_schedule, (1%N, new_round))) in
      let out := (add_to_initial current_digest, 1%N) in
      (new_state, out)
    else
      (* perform compression *)
      let t := N.to_nat round in
      let next_digest :=
          SHA256.sha256_compress msg i (List.resize 0%N 8 current_digest) t in
      let next_message_schedule :=
          if (15 <=? round)%N
          then List.slice 0%N (SHA256.W msg i) (t + 1 - 16) 16
          else message_schedule in
      let new_state := (next_digest, (next_message_schedule, (0%N, new_round))) in
      let out := (add_to_initial next_digest, 0%N) in
      (new_state, out).
*)

Definition state_of {s i o} (c : @Circuit denote_type s i o) : type := s.
Compute state_of sha256_inner.


Lemma nth_skipn {A} (d : A) n i ls :
  nth i (skipn n ls) d = nth (n + i) ls d.
Proof.
  revert i ls; induction n; [ reflexivity | ].
  intros; destruct ls; [ destruct i; reflexivity | ].
  cbn [Nat.add]. autorewrite with push_skipn push_nth.
  rewrite IHn. reflexivity.
Qed.
Hint Rewrite @nth_skipn using solve [eauto] : push_nth.

(* TODO: move *)
Lemma slice_map_nth {A} (d : A) ls start len :
  List.slice d ls start len = List.map (fun i => nth (start + i) ls d) (seq 0 len).
Proof.
  intros; subst. cbv [List.slice].
  rewrite resize_map_nth. apply map_ext; intros.
  autorewrite with push_nth; reflexivity.
Qed.

(* TODO: move *)
Lemma slice_length {A} (d : A) ls start len :
  length (List.slice d ls start len) = len.
Proof. rewrite slice_map_nth. length_hammer. Qed.
Hint Rewrite @slice_length using solve [eauto] : push_length.

(* TODO: move *)
Lemma tl_slice {A} (d : A) ls start len :
  tl (List.slice d ls start (S len)) = List.slice d ls (S start) len.
Proof.
  rewrite !slice_map_nth. cbn [seq List.map tl].
  rewrite <-seq_shift, map_map. apply map_ext; intros.
  f_equal; lia.
Qed.

(* TODO: move *)
Lemma hd_slice {A} (d : A) ls start len :
  hd d (List.slice d ls start (S len)) = nth start ls d.
Proof.
  rewrite !slice_map_nth. cbn [seq List.map hd]. f_equal; lia.
Qed.

(* TODO: move *)
Lemma nth_slice {A} (d : A) ls i start len :
  nth i (List.slice d ls start len) d
  = if i <? len then nth (start + i) ls d else d.
Proof.
  rewrite !slice_map_nth; destruct_one_match;
    autorewrite with push_nth; [ | reflexivity ].
  f_equal; lia.
Qed.
Hint Rewrite @nth_slice using solve [eauto] : push_nth.

(* TODO: move *)
Lemma slice_snoc {A} (d : A) ls start len :
  List.slice d ls start len ++ [nth (start + len) ls d]
  = List.slice d ls start (S len).
Proof.
  rewrite !slice_map_nth. autorewrite with pull_snoc.
  reflexivity.
Qed.

(* TODO: move *)
Lemma slice_0 {A} (d : A) ls len :
  List.slice d ls 0 len = List.resize d len ls.
Proof. reflexivity. Qed.

(* TODO: move *)
Lemma resize_firstn {A} (d : A) ls n m :
  n <= m ->
  List.resize d n (firstn m ls) = List.resize d n ls.
Proof.
  intros; cbv [List.resize]. autorewrite with push_firstn natsimpl push_length.
  repeat (f_equal; try lia).
Qed.

(* TODO: move to SHA256Properties.v *)
Lemma sha256_compress_length msg i H t :
  length (SHA256.sha256_compress msg i H t) = 8.
Proof. reflexivity. Qed.
Hint Rewrite @sha256_compress_length using solve [eauto] : push_length.
Lemma fold_left_sha256_compress_length msg i H ts :
  length H = 8 ->
  length (fold_left (SHA256.sha256_compress msg i) ts H) = 8.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8); auto.
Qed.
Hint Rewrite @fold_left_sha256_compress_length using solve [length_hammer]
  : push_length.
Lemma sha256_step_length msg H i :
  length H = 8 -> length (SHA256.sha256_step msg H i) = 8.
Proof. intros; cbv [SHA256.sha256_step]. length_hammer. Qed.
Hint Rewrite @sha256_step_length using solve [length_hammer] : push_length.
Lemma fold_left_sha256_step_length msg H idxs :
  length H = 8 -> length (fold_left (SHA256.sha256_step msg) idxs H) = 8.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8); auto.
  intros; length_hammer.
Qed.
Hint Rewrite @fold_left_sha256_step_length using solve [length_hammer]
  : push_length.

Ltac is_projection_from_step e :=
  lazymatch e with
  | fst ?e' => is_projection_from_step e'
  | snd ?e' => is_projection_from_step e'
  | step _ _ _ => idtac
  | _ => fail "term is not a projection from step"
  end.

(* works like destruct_pair_let, but only simplifies expressions with step *)
Ltac destruct_step_pair_let :=
  repeat match goal with
         | |- context [match ?p with
                      | pair _ _ => _ end] =>
           is_projection_from_step p;
           rewrite (surjective_pairing p)
         end.

(* TODO : move *)
Ltac boolsimpl_hyps :=
  autorewrite with boolsimpl in *; cbn [negb andb orb xorb] in *;
  repeat lazymatch goal with
         | H : (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H; destruct H
         | H : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H; destruct H
         | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H; destruct H
         | H : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in H; destruct H
         | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
         | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
         end.

(* TODO: move *)
Module N.

  Lemma ltb_ge x y : N.ltb x y = false <-> (x >= y)%N.
  Proof.
    destr (x <? y)%N; split; (discriminate || lia).
  Qed.
  Lemma leb_gt x y : N.leb x y = false <-> (x > y)%N.
  Proof.
    destr (x <=? y)%N; split; (discriminate || lia).
  Qed.

  Ltac bool_to_prop :=
    repeat lazymatch goal with
           | H : (_ =? _)%N = true |- _ => rewrite N.eqb_eq in H
           | H : (_ =? _)%N = false |- _ => rewrite N.eqb_neq in H
           | H : (_ <=? _)%N = true |- _ => rewrite N.leb_le in H
           | H : (_ <=? _)%N = false |- _ => rewrite leb_gt in H
           | H : (_ <? _)%N = true |- _ => rewrite N.ltb_lt in H
           | H : (_ <? _)%N = false |- _ => rewrite N.ltb_ge in H
           end.
End N.

Lemma apply_if {A B} (f : A -> B) (b : bool) x y : f (if b then x else y) = if b then f x else f y.
Proof. destruct b; reflexivity. Qed.
Lemma fst_if {A B} (b : bool) (x y : A * B) : fst (if b then x else y) = if b then fst x else fst y.
Proof. apply apply_if. Qed.
Lemma snd_if {A B} (b : bool) (x y : A * B) : snd (if b then x else y) = if b then snd x else snd y.
Proof. apply apply_if. Qed.
Hint Rewrite @fst_if @snd_if using solve [eauto] : tuple_if.

Lemma step_sha256_inner_invariant
      (input : denote_type [Bit; sha_block; sha_digest; Bit])
      (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
      msg i :
  sha256_inner_pre input msg i ->
  sha256_inner_invariant state msg (fst (snd (snd input))) i ->
  sha256_inner_invariant
    (fst (step sha256_inner state input)) msg (fst (snd (snd input))) i.
Proof.
  destruct input as (block_valid, (block, (initial_digest, (clear, [])))).
  destruct state as (current_digest, (message_schedule, (done, round))).
  pose (t:=round). cbv [sha256_inner_invariant sha256_inner_pre].
  intros ? Hinv. logical_simplify. subst.
  cbv [sha256_inner K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  (* destruct cases for [clear] *)
  lazymatch goal with H : _ \/ clear = 0%N |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb] end;
    (* handle clear = 1 case *)
    [ left; reflexivity | ].
  (* destruct cases for [block_valid] *)
  lazymatch goal with H : _ \/ block_valid = 0%N |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb] end;
    (* handle block_valid = 1 case *)
    [ right; ssplit; auto; lia | ].
  (* destruct cases for [done] *)
  lazymatch goal with H : done = 1%N \/ _ |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb] end;
    (* handle done = 1 case *)
    [ left; destr (round =? 63)%N; reflexivity | ].
  destr (round =? 63)%N; [ left; reflexivity | ].

  (* For remaining cases, the new [done] is always 0 *)
  cbn [N.lor N.eqb]. right.
  (* destruct case statements *)
  repeat first [ discriminate
               | lia
               | destruct_one_match_hyp
               | destruct_one_match ].
  all:try (rewrite (N.mod_small _ (2 ^ N.of_nat 7))
            by (change (2 ^ N.of_nat 7)%N with 128%N; lia)).
  all:rewrite ?resize_noop by length_hammer.
  all:rewrite ?tl_slice, ?hd_slice.
  all:autorewrite with natsimpl.
  all:ssplit;
    lazymatch goal with
    | |- ?x = ?x => reflexivity
    | |- (_ < _)%N => lia
    | _ => idtac
    end.
  (* solve subgoals about compression *)
  all:
    lazymatch goal with
      | |- context [sha256_compress] =>
        erewrite step_sha256_compress with (t:=N.to_nat round)
          by (autorewrite with push_nth; repeat destruct_one_match;
              lia || (f_equal; lia)); cbn [fst snd];
          replace (N.to_nat (round + 1)) with (S (N.to_nat round)) by lia;
      autorewrite with pull_snoc; rewrite resize_noop by length_hammer;
        reflexivity
      | |- _ => idtac
    end.
  (* remaining subgoals should all be about message schedule: solve those *)
  all:lazymatch goal with
        | |- context [sha256_message_schedule_update] =>
          erewrite step_sha256_message_schedule_update with (t:=(N.to_nat round+1))
            by lazymatch goal with
               | |- nth _ _ _ = nth _ _ _ => f_equal; lia
               | _ => lia
               end; cbn [fst snd];
            lazymatch goal with
            | |- context [List.slice ?d ?ls ?start ?len ++ [nth ?n ?ls ?d]] =>
              replace n with (start + len) by lia
            end; rewrite slice_snoc, tl_slice; f_equal; lia
      end.
Qed.

Lemma step_sha256_inner
      (input : denote_type [Bit; sha_block; sha_digest; Bit])
      (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
      msg i :
  sha256_inner_pre input msg i ->
  sha256_inner_invariant state msg (fst (snd (snd input))) i ->
  snd (step sha256_inner state input) = sha256_inner_spec input state msg i.
Proof.
  destruct input as (block_valid, (block, (initial_digest, (clear, [])))).
  destruct state as (current_digest, (message_schedule, (done, round))).
  pose (t:=round). cbv [sha256_inner_invariant sha256_inner_pre sha256_inner_spec].
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_inner K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  stepsimpl. rewrite !resize_noop by length_hammer.
  (* destruct cases for [clear] *)
  lazymatch goal with H : _ \/ clear = 0%N |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb Pos.eqb] end;
    (* handle clear = 1 case *)
    [ rewrite !resize_noop by reflexivity; reflexivity | ].
  (* destruct cases for [block_valid] *)
  lazymatch goal with H : _ \/ block_valid = 0%N |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb Pos.eqb] end;
    (* handle block_valid = 1 case *)
    [ rewrite !resize_noop by length_hammer; reflexivity | ].
  (* destruct cases for [done] *)
  lazymatch goal with H : done = 1%N \/ _ |- _ =>
                      destruct H; logical_simplify; subst; cbn [N.eqb] end;
    (* handle done = 1 case *)
    [ destr (round =? 63)%N;
      rewrite resize_noop with (ls:=fold_left _ _ _) by length_hammer;
      reflexivity | ].

  rewrite !resize_noop by length_hammer.
  erewrite step_sha256_compress with (t:=N.to_nat round)
    by (autorewrite with push_nth; repeat destruct_one_match;
        repeat destruct_one_match_hyp; f_equal; lia).
  cbn [fst snd]. rewrite resize_noop by length_hammer.
  destruct_one_match; reflexivity.
Qed.
