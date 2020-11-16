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
From Coq Require Import derive.Derive.
From Cava Require Import Arrow.ArrowExport Arrow.DeriveSpec
     Arrow.CombinatorProperties BitArithmetic VectorUtils.
Require Import Cava.Tactics.

From Aes Require Import pkg.

Section Wf.
  Lemma aes_transpose_Wf n m : Wf (@aes_transpose n m).
  Proof.
    induction n; cbn [aes_transpose]; prove_Wf.
    { eapply map2_Wf; prove_Wf. }
  Qed.
  Hint Resolve aes_transpose_Wf : Wf.

  Lemma CIPH_FWD_Wf : Wf (CIPH_FWD).
  Proof. cbv [CIPH_FWD]; prove_Wf. Qed.
  Hint Resolve CIPH_FWD_Wf : Wf.

  Lemma CIPH_INV_Wf : Wf (CIPH_INV).
  Proof. cbv [CIPH_INV]; prove_Wf. Qed.
  Hint Resolve CIPH_INV_Wf : Wf.
End Wf.
Hint Resolve aes_transpose_Wf CIPH_FWD_Wf CIPH_INV_Wf : Wf.

Section Equivalence.
  Lemma aes_transpose_correct n m (x : Vector.t (Vector.t (Vector.t bool _) _) _) :
    kinterp (@aes_transpose n m) (x, tt) = transpose_rev x.
  Proof.
    revert m x; induction n; cbn [aes_transpose transpose_rev];
      kappa_spec; [ reflexivity | ].
    repeat destruct_pair_let. cbn [fst snd].
    autorewrite with vsimpl. reflexivity.
  Qed.
  Hint Rewrite @aes_transpose_correct : kappa_interp.
  Opaque aes_transpose.

  Lemma CIPH_FWD_correct : kinterp CIPH_FWD tt = false.
  Proof. cbv [CIPH_FWD]. kappa_spec; reflexivity. Qed.
  Lemma CIPH_INV_correct : kinterp CIPH_INV tt = true.
  Proof. cbv [CIPH_INV]. kappa_spec; reflexivity. Qed.
  Hint Rewrite @CIPH_FWD_correct @CIPH_INV_correct : kappa_interp.
  Opaque CIPH_FWD CIPH_INV.
End Equivalence.
Hint Rewrite @aes_transpose_correct @CIPH_FWD_correct @CIPH_INV_correct
     using solve [eauto] : kappa_interp.
Global Opaque aes_transpose CIPH_FWD CIPH_INV.
