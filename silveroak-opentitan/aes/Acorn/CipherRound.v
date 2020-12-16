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
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Acorn.Acorn.
Require Import AcornAes.Common.
Import Common.Notations.

Local Open Scope monad_scope.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {monad: Monad cava}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state)).

  Definition cipher_round
             (is_decrypt : signal Bit) (input: signal state) (key : signal key)
    : cava (signal state) :=
    (sub_bytes is_decrypt   >=>
     shift_rows is_decrypt  >=>
     mix_columns is_decrypt >=>
     add_round_key key) input.

  Definition cipher
        (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
        (first_key last_key : signal key)
        (middle_keys : list (signal key))
        (input : signal state)
        : cava (signal state) :=
    (add_round_key first_key                      >=>
     foldLM (cipher_round is_decrypt) middle_keys >=>
     sub_bytes is_decrypt                         >=>
     shift_rows is_decrypt                        >=>
     add_round_key last_key) input.

End WithCava.
