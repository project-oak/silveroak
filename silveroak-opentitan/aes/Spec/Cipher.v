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

Require Import Coq.Lists.List.

Hint Rewrite @map_app @fold_left_app : listsimpl.
Local Ltac listsimpl :=
  repeat progress (cbn [rev map fold_left]; autorewrite with listsimpl).

Section Spec.
  Context (state key : Type)
          (add_round_key : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (inv_sub_bytes inv_shift_rows inv_mix_columns : state -> state)
          (inv_mix_columns_key : key -> key).

  (**** FIPS 197, Fig. 15
    EqInvCipher(byte in[4*Nb], byte out[4*Nb], word dw[Nb*(Nr+1)])
    begin
      byte state[4,Nb]
      state = in

      AddRoundKey(state, dw[Nr*Nb, (Nr+1)*Nb-1])

      for round = Nr-1 step -1 downto 1
        InvSubBytes(state)
        InvShiftRows(state)
        InvMixColumns(state)
        AddRoundKey(state, dw[round*Nb, (round+1)*Nb-1])
      end for

      InvSubBytes(state)
      InvShiftRows(state)
      AddRoundKey(state, dw[0, Nb-1])

      out = state
    end
   ***)
  Definition equivalent_inverse_cipher
             (first_key last_key : key) (middle_keys : list key)
             (input : state) : state :=
    let st := input in
    let st := add_round_key st first_key in
    let st := fold_left
                (fun (st : state) (round_key : key) =>
                   let st := inv_sub_bytes st in
                   let st := inv_shift_rows st in
                   let st := inv_mix_columns st in
                   let st := add_round_key st round_key in
                   st)
                middle_keys st in
    let st := inv_sub_bytes st in
    let st := inv_shift_rows st in
    let st := add_round_key st last_key in
    st.

  (**** FIPS 197, Fig. 5
    Cipher(byte in[4*Nb], byte out[4*Nb], word w[Nb*(Nr+1)])
    begin
      byte state[4,Nb]
      state = in

      AddRoundKey(state, w[0, Nb-1])

      for round = 1 step 1 to Nr–1
        SubBytes(state)
        ShiftRows(state)
        MixColumns(state)
        AddRoundKey(state, w[round*Nb, (round+1)*Nb-1])
      end for

      SubBytes(state)
      ShiftRows(state)
      AddRoundKey(state, w[Nr*Nb, (Nr+1)*Nb-1])

      out = state
    end
   ***)
  Definition cipher (first_key last_key : key) (middle_keys : list key)
             (input : state) : state :=
    let st := input in
    let st := add_round_key st first_key in
    let st := fold_left
                (fun (st : state) (round_key : key) =>
                   let st := sub_bytes st in
                   let st := shift_rows st in
                   let st := mix_columns st in
                   let st := add_round_key st round_key in
                   st)
                middle_keys st in
    let st := sub_bytes st in
    let st := shift_rows st in
    let st := add_round_key st last_key in
    st.

  Section Properties.
    Context
      (add_round_key_involutive :
         forall st k, add_round_key (add_round_key st k) k = st)
      (inv_sub_bytes_id : forall st, inv_sub_bytes (sub_bytes st) = st)
      (inv_shift_rows_id : forall st, inv_shift_rows (shift_rows st) = st)
      (inv_mix_columns_id : forall st, inv_mix_columns (mix_columns st) = st)
      (shift_rows_sub_bytes_commute :
         forall st, shift_rows (sub_bytes st) = sub_bytes (shift_rows st))
      (add_round_key_mix_columns_linear :
         forall st k, add_round_key (inv_mix_columns st) (inv_mix_columns_key k)
                 = inv_mix_columns (add_round_key st k)).

    Hint Rewrite add_round_key_involutive inv_sub_bytes_id inv_shift_rows_id
         inv_mix_columns_id : identity.
    Local Ltac t :=
      first [ progress autorewrite with identity
            | rewrite shift_rows_sub_bytes_commute; progress t
            | rewrite add_round_key_mix_columns_linear; progress t
            | reflexivity ].

    Lemma add_round_key_cancel st k b :
      st = add_round_key b k -> add_round_key st k = b.
    Proof. intros; subst; repeat t. Qed.

    Lemma inverse_cipher_id first_key last_key middle_keys block :
      equivalent_inverse_cipher
        last_key first_key
        (map inv_mix_columns_key (rev middle_keys))
        (cipher first_key last_key middle_keys block) = block.
    Proof.
      cbv [cipher equivalent_inverse_cipher].
      apply add_round_key_cancel. revert first_key block.
      induction middle_keys; intros; listsimpl.
      { repeat t. }
      { rewrite IHmiddle_keys. repeat t. }
    Qed.
  End Properties.
End Spec.
