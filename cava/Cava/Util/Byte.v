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
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.

Require Import coqutil.Tactics.Tactics.

Import ListNotations.

Local Open Scope N.

(* Convert the least significant 8 bits of a number to a byte *)
Definition N_to_byte (x : N) : byte :=
  match Byte.of_N (x mod 2^8) with
  | Some b => b
  | None => x00
  end.

Module BigEndianBytes.
  (* evaluate a big-endian list of bytes *)
  Definition concat_bytes (bs : list byte) : N :=
    List.fold_left (fun acc b => N.lor (N.shiftl acc 8) (Byte.to_N b)) bs 0%N.

  (* convert the least significant (n*8) bits of a number to big-endian bytes *)
  Definition N_to_bytes n (x : N) : list byte :=
    List.map (fun i => N_to_byte (N.shiftr x (N.of_nat (n-1-i)*8)))
             (seq 0 n).

  (* convert a big-endian list of bytes to a list of n-byte words (length of list
   must be a multiple of n) *)
  Definition bytes_to_Ns n (x : list byte) : list N :=
    List.map (fun i => concat_bytes (firstn n (skipn (n*i) x))) (seq 0 (length x / n)).
End BigEndianBytes.

Definition byte_xor (x y : byte) : byte := N_to_byte (N.lxor (Byte.to_N x) (Byte.to_N y)).

Module N2Byte.
  Lemma id (x: N) : ((Byte.to_N (N_to_byte x)) = x mod 256)%N.
  Proof.
    cbv [N_to_byte].
    destr (Byte.of_N (x mod 2 ^ 8)).
    { rewrite Byte.to_of_N with (x:=(x mod 2^8)%N) by apply E. reflexivity. }
    { rewrite (Byte.of_N_None_iff (x mod 2^8))%N in E. exfalso.
      pose (N.mod_upper_bound x (2^8))%N.
      assert (2 ^ 8 <> 0)%N by (cbn;lia).
      specialize (l H).
      replace 255%N with (N.pred 256)%N in E by lia.
      apply N.lt_pred_le in E.
      apply N.lt_le_pred in l.
      rewrite l in E.
      cbn in E.
      lia.
    }
  Qed.

End N2Byte.

Module Byte2N.
  Lemma id x: (N_to_byte (Byte.to_N x) = x )%N.
  Proof. destr x; now cbn. Qed.

  Lemma inj x y: (Byte.to_N x = Byte.to_N y -> x = y)%N.
  Proof.  intro H. rewrite <- (id x), <- (id y). now f_equal. Qed.
End Byte2N.

Lemma testbit_byte b n:
  (8 <= n) ->
  N.testbit (Byte.to_N b) n = false.
Proof.
  intros.
  intros.
  remember (Byte.to_N b) as b'.
  pose (Byte.to_N_bounded b).
  apply N.lt_succ_r in l.
  change (N.succ 255) with (2^8) in l.
  rewrite <- Heqb' in l.
  apply N.testbit_high.
  apply (N.lt_le_trans _ (2^8));
    [ lia | apply N.pow_le_mono_r; lia ].
Qed.

Lemma unfold_N_to_bytes_4 x: BigEndianBytes.N_to_bytes 4 x =
  [N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 0) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 1) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 2) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 3) * 8))].
Proof.
  cbv [BigEndianBytes.N_to_bytes].
  now cbn [List.map seq].
Qed.

Lemma shiftr_byte b x: (8 <= x) ->
  N.shiftr (Byte.to_N b) x = 0.
Proof.
  intros.
  remember (Byte.to_N b) as b'.
  pose (Byte.to_N_bounded b).
  apply N.shiftr_eq_0.
  apply N.lt_succ_r in l.
  apply (N.lt_le_trans _ (N.log2 256)).
  {
    destr (0<?b').
    2:{ destr (b'=?0); try rewrite E0; cbn; lia. }
    apply N.log2_lt_pow2. { lia. }
    cbn. now rewrite Heqb'.
  }
  now cbn.
Qed.

Lemma N_to_bytes_length n x : length (BigEndianBytes.N_to_bytes n x) = n.
Proof. cbv [BigEndianBytes.N_to_bytes]. length_hammer. Qed.
Hint Rewrite @N_to_bytes_length : push_length.

Lemma bytes_to_Ns_length n bs:
  (length (BigEndianBytes.bytes_to_Ns n bs) = length bs / n)%nat.
Proof. cbv [BigEndianBytes.bytes_to_Ns]. length_hammer. Qed.
Hint Rewrite @bytes_to_Ns_length : push_length.

Lemma N_to_byte_to_N x : Byte.to_N (N_to_byte x) = (x mod 256)%N.
Proof.
  cbv [N_to_byte]. change (2 ^ 8)%N with 256%N.
  pose proof N.mod_bound_pos x 256 ltac:(lia) ltac:(lia).
  pose proof proj1 (Byte.of_N_None_iff (x mod 256)).
  apply Byte.to_of_N.
  destruct (Byte.of_N (x mod 256)); [ reflexivity | ].
  lazymatch goal with H : None = None -> _ |- _ =>
                      specialize (H ltac:(reflexivity)) end.
  lia.
Qed.

Lemma nth_bytes_to_Ns i n bs :
  (length bs mod n = 0)%nat ->
  (n <> 0)%nat ->
  List.nth i (BigEndianBytes.bytes_to_Ns n bs) 0%N
  = BigEndianBytes.concat_bytes
      (List.map
         (fun j => List.nth (i*n + j) bs Byte.x00)
         (seq 0 n)).
Proof.
  cbv [BigEndianBytes.bytes_to_Ns]. intros.
  destruct (Compare_dec.lt_dec i (length bs / n)).
  { erewrite map_nth_inbounds with (d2:=0%nat) by length_hammer.
    cbv [BigEndianBytes.concat_bytes]. f_equal; [ ].
    push_nth. natsimpl.
    erewrite firstn_map_nth with (d:=Byte.x00).
    { eapply List.map_ext_in; intros *.
      rewrite in_seq; natsimpl; intros.
      push_nth. f_equal; lia. }
    { push_length.
      Zify.zify.
      (* extra step because zify fails to zify Nat.modulo and Nat.div *)
      rewrite ?mod_Zmod, ?div_Zdiv in * by lia.
      Zify.zify; Z.to_euclidean_division_equations.
      (* N.B. this needs nia instead of lia *)
      nia. } }
  { push_nth. cbv [BigEndianBytes.concat_bytes].
    assert (length bs <= i * n)%nat.
    { Zify.zify.
      (* extra step because zify fails to zify Nat.modulo and Nat.div *)
      rewrite ?mod_Zmod, ?div_Zdiv in * by lia.
      Zify.zify; Z.to_euclidean_division_equations.
      (* N.B. this needs nia instead of lia *)
      nia. }
    apply fold_left_invariant with (I:= eq 0%N); [ reflexivity | | tauto ].
    intros *; rewrite in_map_iff.
    intros; logical_simplify; subst.
    match goal with H : _ |- _ => apply in_seq in H end.
    push_nth. reflexivity. }
Qed.

Lemma N_to_byte_equiv x y :
  (x mod 256 = y mod 256)%N -> N_to_byte x = N_to_byte y.
Proof.
  intro Heq. cbv [N_to_byte]. compute_expr (2 ^ 8)%N.
  rewrite Heq. reflexivity.
Qed.

Lemma nth_N_to_bytes i n x :
  (i < n)%nat ->
  List.nth i (BigEndianBytes.N_to_bytes n x) Byte.x00
  = N_to_byte (N.shiftr (N.land x (N.ones (8 * N.of_nat n)))
                        (N.of_nat (n - 1 - i) * 8)).
Proof.
  intros. cbv [BigEndianBytes.N_to_bytes].
  push_nth; natsimpl. apply N_to_byte_equiv.
  change 256%N with (2 ^ 8)%N.
  apply N.bits_inj; intro j.
  push_Ntestbit; boolsimpl.
  case_eq (j <? 8)%N; intros; N.bool_to_prop; [ | reflexivity ].
  push_Ntestbit. boolsimpl.
  f_equal; lia.
Qed.

