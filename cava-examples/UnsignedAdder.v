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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import Hask.Control.Monad.

Require Import Cava.
Require Import FullAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* An unsigned addder which takes two size N bit-vectors and a carry in
   and returns a sized N+1 result which is the addition of the two
   input vectors and carry in.
*)

Fixpoint unsignedAdder {m bit} `{Cava m bit}
                       (n : nat) (a : list bit) (b : list bit) (cin : bit)
  : m (list bit)
  :=
  match n with
  | 0 => return_ [cin]
  | S n  => sum_cout <- fullAdderFC (hd cin a) (hd cin b) cin ;
            let sum := fst sum_cout in
            let cout := snd sum_cout in 
            r <- unsignedAdder n (tl a) (tl b) cout ;
            return_ (cons sum r)
  end.

Definition adder8 := unsignedAdder 8.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Definition toVec := map nat2bool.

Definition bool2nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Definition fromVec := map bool2nat.

Definition v1 := toVec [0;1;0;0;0;0;0;0].
Definition v2 := toVec [1;0;0;0;0;0;0;0].

Compute (fromVec (combinational (adder8 v1 v2 false))).

Definition v3 := toVec [1;1;1;1;1;1;1;1].
Definition v4 := toVec [1;0;0;0;0;0;0;0].

Compute (fromVec (combinational (adder8 v3 v4 false))).

Definition v5 := toVec [1;1;1;1;1;1;1;1].
Definition v6 := toVec [1;1;1;1;1;1;1;1].

Compute (fromVec (combinational (adder8 v5 v6 true))).