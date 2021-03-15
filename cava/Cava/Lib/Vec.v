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

Require Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Require Import Cava.Core.Core.
Require Import Cava.Util.Vector.
Import MonadNotation.
Import Vector.VectorNotations.
Local Open Scope monad_scope.
Local Open Scope vector_scope.

Section WithCava.
  Context `{semantics:Cava}.

  Definition bitvec_literal {n} (v : Vector.t bool n)
    : cava (signal (Vec Bit n)) :=
    packV (Vector.map constant v).

  Definition nil {A} : cava (signal (Vec A 0)) :=
    packV [].

  Definition cons {A n} (a : signal A) (v : signal (Vec A n))
    : cava (signal (Vec A (S n))) :=
    v <- unpackV v ;;
    packV (a :: v).

  Definition tl {A n} (v : signal (Vec A (S n))) : cava (signal (Vec A n)) :=
    v <- unpackV v ;;
    packV (Vector.tl v).

  Definition hd {A n} (v : signal (Vec A (S n))) : cava (signal A) :=
    v <- unpackV v ;;
    ret (Vector.hd v).

  Definition const {A} (x : signal A) n
    : cava (signal (Vec A n)) :=
    packV (Vector.const x n).

  Definition rev {A n} (v : signal (Vec A n))
    : cava (signal (Vec A n)) :=
    v <- unpackV v ;;
    packV (Vector.rev v).

  Definition last {A n} (v : signal (Vec A (S n)))
    : cava (signal A) :=
    v <- unpackV v ;;
    ret (Vector.last v).

  Definition shiftin {A n} (x : signal A) (v : signal (Vec A n))
    : cava (signal (Vec A (S n))) :=
    v <- unpackV v ;;
    packV (Vector.shiftin x v).

  Definition shiftout {A n} (v : signal (Vec A (S n)))
    : cava (signal (Vec A n)) :=
    v <- unpackV v ;;
    packV (Vector.shiftout v).

  Definition transpose {A n m} (v : signal (Vec (Vec A n) m))
    : cava (signal (Vec (Vec A m) n)) :=
    v <- unpackV v ;;
    v <- Traversable.mapT unpackV v ;;
    v <- Traversable.mapT packV (transpose v) ;;
    packV v.

  Fixpoint fold_left {A B}
             (f : B * signal A -> cava B)
             {n}
    : signal (Vec A n) -> B -> cava B :=
    match n with
    | 0 => fun v st => ret st
    | S n => fun v st =>
              v0 <- hd v ;;
              st' <- f (st, v0) ;;
              v' <- tl v ;;
              fold_left f v' st'
    end.

  Fixpoint fold_left2 {A B C}
             (f : C * signal A * signal B -> cava C)
             {n}
    : signal (Vec A n) -> signal (Vec B n) -> C -> cava C :=
    match n with
    | 0 => fun va vb st => ret st
    | S n => fun va vb st =>
              va0 <- hd va ;;
              vb0 <- hd vb ;;
              st' <- f (st, va0, vb0) ;;
              va' <- tl va ;;
              vb' <- tl vb ;;
              fold_left2 f va' vb' st'
    end.

  Definition map {A B n} (f : signal A -> cava (signal B))
             (v : signal (Vec A n))
    : cava (signal (Vec B n)) :=
    v <- unpackV v ;;
    out <- Traversable.mapT f v ;;
    packV out.

  Definition map2 {A B C n}
             (f : signal A * signal B -> cava (signal C))
             (va : signal (Vec A n)) (vb : signal (Vec B n))
    : cava (signal (Vec C n)) :=
    va <- unpackV va ;;
    vb <- unpackV vb ;;
    out <- Traversable.mapT f (vcombine va vb) ;;
    packV out.
End WithCava.
