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

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaClass.

(******************************************************************************)
(* Inductive to capture circuit's sequential structure                        *)
(******************************************************************************)

Section WithCava.
  Context `{semantics:Cava}.

  (* TODO: change loop here to a loop with enable *)
  (* TODO: maybe make loop have separate in/out types to reduce state info *)
  Inductive Circuit : Type -> Type -> Type :=
  | Comb : forall {i o}, (i -> cava o) -> Circuit i o
  | Compose : forall {i t o}, Circuit i t -> Circuit t o -> Circuit i o
  | First : forall {i o t}, Circuit i o -> Circuit (i * t) (o * t)
  | Second : forall {i o t}, Circuit i o -> Circuit (t * i) (t * o)
  | Loop :
      forall {i s : Type},
        Circuit (i * s) s ->
        Circuit i s
  | Delay : forall {t}, Circuit t t
  .

  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : Type :=
    match c with
    | Comb _ => unit
    | Compose f g => circuit_state f * circuit_state g
    | First f => circuit_state f
    | Second f => circuit_state f
    | @Loop i s f => circuit_state f * s
    | @Delay t => t
    end.

  (* Run circuit for a single step *)
  Fixpoint interp {i o} (c : Circuit i o)
    : circuit_state c -> i -> cava (o * circuit_state c) :=
    match c in Circuit i o return circuit_state c -> i
                                  -> cava (o * circuit_state c) with
    | Comb f => fun _ i => x <- f i ;; ret (x, tt)
    | Compose f g =>
      fun cs input =>
        '(x, cs1) <- interp f (fst cs) input ;;
        '(y, cs2) <- interp g (snd cs) x ;;
        ret (y, (cs1, cs2))
    | First f =>
      fun cs input =>
        '(x, cs') <- interp f cs (fst input) ;;
        ret (x, snd input, cs')
    | Second f =>
      fun cs input =>
        '(x, cs') <- interp f cs (snd input) ;;
        ret (fst input, x, cs')
    | @Loop i s f =>
      fun cs input =>
        '(x, cs') <- interp f (fst cs) (input, snd cs) ;;
        ret (x, (cs', x))
    | Delay =>
      fun cs input =>
        ret (cs, input)
    end.
End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
