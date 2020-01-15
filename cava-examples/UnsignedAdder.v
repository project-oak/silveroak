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

(*

Need to rework to make decreasing argument clear.

Fixpoint unsignedAdder {m bit} `{Cava m bit}
                       (n:N) (a : list bit) (b : list bit) (cin : bit)
  : m (list bit)
  :=
  match n with
  | N0 => return_ []
  | s  => sum_cout <- fullAdderFC (hd cin a) (hd cin b) cin ;
         r <- unsignedAdder (n - 1) (tl a) (tl b) (snd sum_cout) ;
         return_ (cons (fst sum_cout) r)
  end.


*)