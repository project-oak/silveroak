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
Require Import Cava.ListUtils.

Section Spec.
  Context {byte : Type} (Nb : nat).
  Local Notation word := (list byte) (only parsing).
  Local Notation state := (list word) (only parsing).

  Definition shift_row (w : word) (r : nat) :=
    skipn r w ++ firstn r w.

  Definition shift_rows (st : state) :=
    map2 shift_row st (List.seq 0 Nb).

  Definition inv_shift_rows (st : state) :=
    map2 shift_row st (rev (List.seq 1 Nb)).
End Spec.

Section BasicTests.
  Import ListNotations.

  (* use nat as the "byte" type so shifting is easy to read *)
  Definition nat_rows := [[0; 1; 2; 3]; [4; 5; 6; 7]; [8; 9; 10; 11]; [12; 13; 14; 15]].
  Definition shifted_nat_rows := [[0; 1; 2; 3]; [5; 6; 7; 4]; [10; 11; 8; 9]; [15; 12; 13; 14]].

  Goal (shift_rows 4 nat_rows = shifted_nat_rows).
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows 4 shifted_nat_rows = nat_rows).
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows 4 (shift_rows 4 nat_rows) = nat_rows).
  Proof. vm_compute. reflexivity. Qed.
End BasicTests.
