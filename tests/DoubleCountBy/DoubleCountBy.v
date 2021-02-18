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

Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Lib.UnsignedAdders.
Import Circuit.Notations.

(******************************************************************************)
(* DoubleCountBy                                                              *)
(******************************************************************************)

(*

This circuit extends the countBy circuit to have a loop within a loop; the outer
counter gets incremented when the inner counter overflows.

                _______
    -----------| delay |-----------.
   |           |_______|           |
   |                      _        |
   |---------------------| \       |
   |    ______           |  |------------ out
   '---| incr |----------|_/
       |______|           |
          _______         |
      .--| delay |--.     |
      |  |_______|  |     |
      |     ___     |     | carry
      '----|   |----'     |
           | + |          |
 in--------|___|-------- -'

*)

Section WithCava.
  Context {signal} {semantics: Cava signal}.

  Definition ltV {m n} (xy : signal (Vec Bit n) * signal (Vec Bit m))
    : cava (signal Bit) := inv (greaterThanOrEqual (snd xy, fst xy)).

  (* add-with-carry *)
  Definition addC {n} (xy : signal (Vec Bit n) * signal (Vec Bit n))
    : cava (signal (Vec Bit n) * signal Bit) :=
    sum <- addN xy ;;
    carry <- ltV (fst xy, sum) ;;
    ret (sum,carry).

  (* incrementer *)
  Definition incrN {n} (x : signal (Vec Bit (S n)))
    : cava (signal (Vec Bit (S n))) :=
    let one : signal (Vec Bit 1) := unpeel [constant true]%vector in
    let xp1 : signal (Vec Bit (S (Nat.max 1 (S n)))) := unsignedAdd (one, x) in
    ret (unpeel (shiftout (peel xp1))).

  Definition count_by
    : Circuit (signal (Vec Bit 8)) (signal (Vec Bit 8) * signal Bit)
    := Loop (Comb (fun '(i,(s,_)) => addC (i, s))).

  Definition double_count_by
    : Circuit (signal (Vec Bit 8)) (signal (Vec Bit 8))
    := Loop ((First count_by) (* acc1, carry1, acc2 *)
               >==>
               Comb (fun '(acc1,carry1, acc2) =>
                       acc2p1 <- incrN acc2 ;;
                       muxPair carry1 (acc2, acc2p1))).
End WithCava.

(* Convenience notations for certain bytes *)
Definition b0 := N2Bv_sized 8 0.
Definition b1 := N2Bv_sized 8 1.
Definition b3 := N2Bv_sized 8 3.
Definition b4 := N2Bv_sized 8 4.
Definition b7 := N2Bv_sized 8 7.
Definition b8 := N2Bv_sized 8 8.
Definition b14 := N2Bv_sized 8 14.
Definition b15 := N2Bv_sized 8 15.
Definition b18 := N2Bv_sized 8 18.
Definition b21 := N2Bv_sized 8 21.
Definition b24 := N2Bv_sized 8 24.
Definition b250 := N2Bv_sized 8 250.
Definition b251 := N2Bv_sized 8 251.

Goal (multistep
        (Comb addC) tt
        [(b14,b0); (b7,b14); (b3,b4); (b24,b250)]
      = [(b14,false);(b21,false);(b7,false);(b18,true)]).
Proof. vm_compute. reflexivity. Qed.

Goal (multistep
        (Comb incrN) tt
        [b14; b7; b3; b250] = [b15;b8;b4;b251]).
Proof. vm_compute. reflexivity. Qed.

Goal (multistep
        count_by
        (tt, (defaultCombValue _, defaultCombValue _))
        [b14; b7; b3; b250] = [(b14,false);(b21,false);(b24,false);(b18,true)]).
Proof. vm_compute. reflexivity. Qed.

Goal (multistep
        double_count_by
        (tt, (defaultCombValue _, defaultCombValue _), tt, defaultCombValue _)
        [b14; b7; b3; b250]
      = [b0;b0;b0;b1]).
Proof. reflexivity. Qed.

(* TODO: netlist generation  -- define a recursive function on Circuit that wires up the netlist *)
