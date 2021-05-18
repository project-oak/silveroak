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

Require Import Coq.NArith.NArith.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import Cava.Core.Core.
Require Import Cava.Util.Vector.
Require Coq.Vectors.Vector.
Import MonadNotation.
Import Vector.VectorNotations.
Local Open Scope monad_scope.
Local Open Scope vector_scope.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

Section WithCava.
  Context `{semantics:Cava}.

  (****************************************************************************)
  (* Convert back and forth from Cava and Coq vectors                         *)
  (****************************************************************************)

  Definition bitvec_literal {n} (v : Vector.t bool n) : signal (Vec Bit n) :=
    constantV (Vector.map constant v).

  Definition of_N {n} (x : N) : signal (Vec Bit n)
    := bitvec_literal (N2Bv_sized n x).

  Definition map_literal {A B n} (f : A -> cava (signal B)) (v : Vector.t A n)
    : cava (signal (Vec B n)) :=
    out <- mapT f v ;;
    packV out.

  Definition unpackV2 {A n0 n1}
    : signal (Vec (Vec A n0) n1)
      -> cava (Vector.t (Vector.t (signal A) n0) n1) :=
    unpackV >=> mapT unpackV.

  Definition unpackV3 {A n0 n1 n2}
    : signal (Vec (Vec (Vec A n0) n1) n2)
      -> cava (Vector.t (Vector.t (Vector.t (signal A) n0) n1) n2) :=
    unpackV >=> mapT unpackV >=> mapT (mapT unpackV).

  Definition unpackV4 {A n0 n1 n2 n3}
    : signal (Vec (Vec (Vec (Vec A n0) n1) n2) n3)
      -> cava (Vector.t (Vector.t (Vector.t (Vector.t (signal A) n0)
                                           n1) n2) n3) :=
    unpackV >=> mapT unpackV >=> mapT (mapT unpackV)
            >=> mapT (mapT (mapT unpackV)).

  Definition packV2 {A n0 n1}
    : Vector.t (Vector.t (signal A) n0) n1
      -> cava (signal (Vec (Vec A n0) n1)) :=
    mapT packV >=> packV.

  Definition packV3 {A n0 n1 n2}
    : Vector.t (Vector.t (Vector.t (signal A) n0) n1) n2
      -> cava (signal (Vec (Vec (Vec A n0) n1) n2)) :=
    mapT (mapT packV) >=> mapT packV >=> packV.

  Definition packV4 {A n0 n1 n2 n3}
    : Vector.t (Vector.t (Vector.t (Vector.t (signal A) n0) n1) n2) n3
      -> cava (signal (Vec (Vec (Vec (Vec A n0) n1) n2) n3)) :=
    mapT (mapT (mapT packV)) >=> mapT (mapT packV) >=> mapT packV >=> packV.

  (****************************************************************************)
  (* Vec versions of operations from Vector standard library                  *)
  (****************************************************************************)

  Definition nil {A} : cava (signal (Vec A 0)) := packV [].

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

  (* N.B. This uses reverse instead of Vector.rev because the latter has proof
     terms in it, which slows down computations *)
  Definition rev {A n} (v : signal (Vec A n))
    : cava (signal (Vec A n)) :=
    v <- unpackV v ;;
    packV (Vector.reverse v).

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

  (****************************************************************************)
  (* Vec versions of operations from Util.Vector library                      *)
  (****************************************************************************)

  Definition transpose {A n m} (v : signal (Vec (Vec A n) m))
    : cava (signal (Vec (Vec A m) n)) :=
    v <- unpackV2 v ;;
    packV2 (transpose v).

  Definition reshape {A n m} (v : signal (Vec A (n * m)))
    : cava (signal (Vec (Vec A m) n)) :=
    v <- unpackV v ;;
    packV2 (reshape v).

  Definition flatten {A n m} (v : signal (Vec (Vec A m) n))
    : cava (signal (Vec A (n * m))) :=
    v <- unpackV2 v ;;
    packV (flatten v).

  (* Coerce the size of a vector to a different size; should only be used if the
     vector sizes are in fact equal (for instance, to coerce n + n to n * 2) *)
  Definition resize_default {A} m {n} (v : signal (Vec A n))
    : cava (signal (Vec A m)) :=
    v <- unpackV v ;;
    packV (resize_default defaultSignal m v).

  (****************************************************************************)
  (* Higher-order functions on vectors                                        *)
  (****************************************************************************)

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
    : signal (Vec A n) * signal (Vec B n) -> C -> cava C :=
    match n with
    | 0 => fun _ st => ret st
    | S n => fun '(va, vb) st =>
              va0 <- hd va ;;
              vb0 <- hd vb ;;
              st' <- f (st, va0, vb0) ;;
              va' <- tl va ;;
              vb' <- tl vb ;;
              fold_left2 f (va', vb') st'
    end.

  Definition map {A B n} (f : signal A -> cava (signal B))
             (v : signal (Vec A n))
    : cava (signal (Vec B n)) :=
    v <- unpackV v ;;
    out <- mapT f v ;;
    packV out.

  Definition map2 {A B C n}
             (f : signal A * signal B -> cava (signal C))
             (i : signal (Vec A n) * signal (Vec B n))
    : cava (signal (Vec C n)) :=
    va <- unpackV (fst i) ;;
    vb <- unpackV (snd i) ;;
    out <- mapT f (vcombine va vb) ;;
    packV out.

  (****************************************************************************)
  (* Boolean operations on bit vectors                                        *)
  (****************************************************************************)

  Definition inv {n} (v : signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map inv v.

  Definition and {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 and2 i.

  Definition nand {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 nand2 i.

  Definition or {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 or2 i.

  Definition nor {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 nor2 i.

  Definition xor {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 xor2 i.

  Definition xnor {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 xnor2 i.

  Definition xorcy {n} (i : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n)) :=
    map2 xorcy i.
End WithCava.

Module BitVecNotations.
  Declare Scope bitvec_scope.
  Delimit Scope bitvec_scope with bv.

  Notation "x & y & .. & z" :=
    ((fun a =>
        bind (and (a,y))
             .. (fun a => bind (and (a,z)) ret) .. ) x)
      (at level 25, left associativity, z at next level, only parsing) : bitvec_scope.

  Notation "x | y | .. | z" :=
    ((fun a =>
        bind (or (a,y))
             .. (fun a => bind (or (a,z)) ret) .. ) x)
      (at level 25, left associativity, z at next level, only parsing) : bitvec_scope.

  Notation "x ^ y ^ .. ^ z" :=
    ((fun a =>
        bind (xor (a,y))
             .. (fun a => bind (xor (a,z)) ret) .. ) x)
      (at level 25, left associativity, z at next level, only parsing) : bitvec_scope.
End BitVecNotations.
