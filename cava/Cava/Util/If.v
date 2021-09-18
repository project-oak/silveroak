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

Lemma apply_if {A B} (f : A -> B) (b : bool) x y : f (if b then x else y) = if b then f x else f y.
Proof. destruct b; reflexivity. Qed.

Lemma fst_if {A B} (b : bool) (x y : A * B) : fst (if b then x else y) = if b then fst x else fst y.
Proof. apply apply_if. Qed.
Lemma snd_if {A B} (b : bool) (x y : A * B) : snd (if b then x else y) = if b then snd x else snd y.
Proof. apply apply_if. Qed.
Hint Rewrite @fst_if @snd_if using solve [eauto] : tuple_if.

Lemma tup_if {A B} (b : bool) (x y: A) (z w: B) : (if b then x else y, if b then z else w) = if b then (x,z) else (y, w).
Proof. destruct b; reflexivity. Qed.
Hint Rewrite @tup_if using solve [eauto] : tuple_if.

Lemma apply_if_ext_1 {A B C} (f : A -> B -> C) (b : bool) x y z : f (if b then x else y) z = if b then f x z else f y z.
Proof. destruct b; reflexivity. Qed.

