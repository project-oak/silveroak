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

Import ListNotations.

Section denote.
  Context {A: Type}.
  Context (denote: A -> Type).

  Fixpoint denote_list (xs: list A): Type :=
    match xs with
    | [] => unit
    | x :: xs => denote x * denote_list xs
    end.

  Fixpoint split_denotation {x y}
    : denote_list (x ++ y) -> denote_list x * denote_list y :=
    match x with
    | [] => fun v => (tt, v)
    | x :: xs => fun '(a,bc) =>
      let (b,c) := split_denotation bc in
      (a,b,c)
    end.

  Fixpoint combine_denotation {x y}
    : denote_list x -> denote_list y -> denote_list (x ++ y) :=
    match x with
    | [] => fun _ y => y
    | x :: xs => fun '(a,b) y =>
      (a, combine_denotation b y)
    end.
End denote.
