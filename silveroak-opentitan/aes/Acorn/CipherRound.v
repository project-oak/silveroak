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

From Coq Require Import Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Import MonadNotation.

From Cava Require Import VectorUtils.
From Cava Require Import Acorn.Acorn.
From Cava Require Import Acorn.Lib.AcornVectors.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} {cava : Cava signal}.
  Context {monad: Monad m}.

  Local Notation state := (Vec (Vec (Vec Bit 8) 4) 4)
                          (only parsing).

  Local Notation key := (Vec (Vec (Vec Bit 8) 4) 4)
                          (only parsing).

  Context (sub_bytes:     signal state -> m (signal state))
          (shift_rows:    signal state -> m (signal state))
          (mix_columns:   signal state -> m (signal state))
          (add_round_key: signal key -> signal state -> m (signal state)).

  (* Perform the bitwise XOR of two 4-element vectors of 8-bit values. *)
  Definition xor4xV
      (ab : signal (Vec (Vec Bit 8) 4) * signal (Vec (Vec Bit 8) 4))
      : m (signal (Vec (Vec Bit 8) 4)) :=
    zipWith xorV (fst ab) (snd ab).

  (* Perform the bitwise XOR of two 4x4 matrices of 8-bit values. *)
  Definition xor4x4V (a b : signal state) : m (signal state) :=
    zipWith xor4xV a b.

  Definition cipher_round (input: signal state) (key : signal key)
    : m (signal state) :=
    stage1 <- sub_bytes input ;;
    stage2 <- shift_rows stage1 ;;
    stage3 <- mix_columns stage2 ;;
    xor4x4V key stage3.

  Local Open Scope list_scope.

  Definition cipher
        (first_key last_key : signal key)
        (middle_keys : list (signal (key)))
        (input : signal (Vec (Vec (Vec Bit 8) 4) 4))
        : m (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
    st1 <- add_round_key first_key input ;;
    st2 <- foldLM cipher_round middle_keys st1 ;;
    st3 <- sub_bytes st2 ;;
    st4 <- shift_rows st3 ;;
    st5 <- add_round_key last_key st4 ;;
    ret st5.

  Definition cipher_alt
        (first_key last_key : signal (Vec (Vec (Vec Bit 8) 4) 4))
        (middle_keys : list (signal (Vec (Vec (Vec Bit 8) 4) 4)))
        (input : signal (Vec (Vec (Vec Bit 8) 4) 4))
        : m (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
    (add_round_key first_key         >=> 
     foldLM cipher_round middle_keys >=> 
     sub_bytes                       >=> 
     shift_rows                      >=> 
     add_round_key last_key) input. 

End WithCava.
