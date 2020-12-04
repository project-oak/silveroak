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
Require Export ExtLib.Data.Monads.IdentityMonad.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Lib.AcornFullAdder.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} {cava : Cava signal}.
  Context {monad: Monad m}.

  (* Vector verison *)

  Definition unsignedAdderV {n : nat}
            (inputs: signal Bit * (Vector.t (signal Bit * signal Bit)) n) :
            m (Vector.t (signal Bit) n * signal Bit) :=
    colV fullAdder inputs.

  Definition adderWithGrowthV {n : nat}
                              (inputs: signal Bit * (Vector.t (signal Bit * signal Bit)) n) :
                              m (Vector.t (signal Bit) (n + 1)) :=
    '(sum, cout) <- unsignedAdderV inputs ;;
    ret (sum ++ [cout]).

  Definition adderWithGrowthNoCarryInV {n : nat}
            (inputs: Vector.t (signal Bit * signal Bit) n) :
            m (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthV (zero, inputs).


  Definition addLWithCinV {n : nat}
                          (cin : signal Bit)
                          (a b : Vector.t (signal Bit) n) :
                          m (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthV (cin, vcombine a b).

  Definition addV {n : nat}
            (a b: Vector.t (signal Bit) n) :
            m (Vector.t (signal Bit) (n + 1)) :=
    adderWithGrowthNoCarryInV (vcombine a b).

  Local Close Scope vector_scope.

  Local Open Scope list_scope.

  (* List version *)

  Definition unsignedAdderL (inputs: signal Bit * (list (signal Bit * signal Bit))) :
                            m (list (signal Bit) * signal Bit) :=
    colL fullAdder inputs.

  Definition adderWithGrowthL (inputs: signal Bit * (list (signal Bit * signal Bit))) :
                              m (list (signal Bit)) :=
    '(sum, cout) <- unsignedAdderL inputs ;;
    ret (sum ++ [cout]).

  Definition adderWithGrowthNoCarryInL
            (inputs: list (signal Bit * signal Bit)) :
            m (list (signal Bit)) :=
    adderWithGrowthL (zero, inputs).

  Definition addLWithCinL (cin : signal Bit)
                          (a b : list (signal Bit)) :
                          m (list (signal Bit)) :=
    adderWithGrowthL (cin, combine a b).

  Definition addL (a b : list (signal Bit)) :
                  m (list (signal Bit)) :=
    adderWithGrowthNoCarryInL (combine a b).

End WithCava.
