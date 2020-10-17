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
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import VectorNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

From Cava Require Import VectorUtils.
From Cava Require Import Acorn.Acorn.
From Cava Require Import Acorn.Lib.AcornFullAdder.

Local Open Scope vector_scope.

(* Vector verison *)

Definition unsignedAdderV {m signal} `{Cava m signal} {n : nat}
           (inputs: signal BitType * (Vector.t (signal BitType * signal BitType)) n) :
           m (Vector.t (signal BitType) n * signal BitType) :=
  colV fullAdder inputs.

Definition adderWithGrowthV {m signal} `{Cava m signal} {n : nat}
                            (inputs: signal BitType * (Vector.t (signal BitType * signal BitType)) n) :
                            m (Vector.t (signal BitType) (n + 1)) :=
  '(sum, cout) <- unsignedAdderV inputs ;;
  ret (sum ++ [cout]).

Definition adderWithGrowthNoCarryInV
           {m signal} `{Cava m signal} {n : nat}
           (inputs: Vector.t (signal BitType * signal BitType) n) :
           m (Vector.t (signal BitType) (n + 1)) :=
  adderWithGrowthV (zero, inputs).


Definition addLWithCinV {m signal} `{Cava m signal} {n : nat}
                        (cin : signal BitType)
                        (a b : Vector.t (signal BitType) n) :
                        m (Vector.t (signal BitType) (n + 1)) :=
  adderWithGrowthV (cin, vcombine a b).

Definition addV
           {m signal} `{Cava m signal} {n : nat}
           (a b: Vector.t (signal BitType) n) :
           m (Vector.t (signal BitType) (n + 1)) :=
  adderWithGrowthNoCarryInV (vcombine a b).

Local Close Scope vector_scope.

Local Open Scope list_scope.

(* List version *)

Definition unsignedAdderL {m signal} `{Cava m signal}
                          (inputs: signal BitType * (list (signal BitType * signal BitType))) :
                          m (list (signal BitType) * signal BitType) :=
  colL fullAdder inputs.

Definition adderWithGrowthL {m signal} `{Cava m signal}
                            (inputs: signal BitType * (list (signal BitType * signal BitType))) :
                            m (list (signal BitType)) :=
  '(sum, cout) <- unsignedAdderL inputs ;;
  ret (sum ++ [cout]).

Definition adderWithGrowthNoCarryInL
           {m signal} `{Cava m signal}
           (inputs: list (signal BitType * signal BitType)) :
           m (list (signal BitType)) :=
  adderWithGrowthL (zero, inputs).

Definition addLWithCinL {m signal} `{Cava m signal}
                        (cin : signal BitType)
                        (a b : list (signal BitType)) :
                        m (list (signal BitType)) :=
  adderWithGrowthL (cin, combine a b).

Definition addL {m signal} `{Cava m signal}
                (a b : list (signal BitType)) :
                m (list (signal BitType)) :=
  adderWithGrowthNoCarryInL (combine a b).

Local Close Scope list_scope.  