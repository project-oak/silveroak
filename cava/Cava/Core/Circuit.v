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

Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Import VectorNotations MonadNotation.

Require Import Cava.Core.CavaClass.
Require Import Cava.Core.Signal.

(******************************************************************************)
(* Inductive to capture circuit's sequential structure                        *)
(******************************************************************************)

Section WithCava.
  Context `{semantics:Cava}.

  Inductive Circuit : Type -> Type -> Type :=
  | Comb : forall {i o}, (i -> cava o) -> Circuit i o
  | Compose : forall {i t o}, Circuit i t -> Circuit t o -> Circuit i o
  | First : forall {i o t}, Circuit i o -> Circuit (i * t) (o * t)
  | Second : forall {i o t}, Circuit i o -> Circuit (t * i) (t * o)
  | LoopInitCE :
      forall {i o : Type} {s : SignalType} (resetval : combType s),
        Circuit (i * signal s) (o * signal s) ->
        Circuit (i * signal Bit) o
  | DelayInitCE :
      forall {t} (resetval : combType t),
        Circuit (signal t * signal Bit) (signal t)
  .

  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : Type :=
    match c with
    | Comb _ => unit
    | Compose f g => circuit_state f * circuit_state g
    | First f => circuit_state f
    | Second f => circuit_state f
    | @LoopInitCE i o s _ f => circuit_state f * combType s
    | @DelayInitCE t _ => combType t
    end.

  (* The state of the circuit after a reset *)
  Fixpoint reset_state {i o} (c : Circuit i o) : circuit_state c :=
    match c as c return circuit_state c with
    | Comb _ => tt
    | Compose f g => (reset_state f, reset_state g)
    | First f => reset_state f
    | Second f => reset_state f
    | LoopInitCE resetval f => (reset_state f, resetval)
    | DelayInitCE resetval => resetval
    end.

  (* Loop with no enable; set enable to always be true *)
  Definition LoopInit {i o s} (resetval : combType s)
             (body : Circuit (i * signal s) (o * signal s))
    : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true))) (LoopInitCE resetval body).
  (* Delay with no enable; set enable to always be true *)
  Definition DelayInit {t} (resetval : combType t)
    : Circuit (signal t) (signal t) :=
    Compose (Comb (fun i => ret (i, constant true))) (DelayInitCE resetval).

  (* Loop with the default signal as its reset value *)
  Definition LoopCE {i o s}
    : Circuit (i * signal s) (o * signal s) -> Circuit (i * signal Bit) o :=
    LoopInitCE (defaultCombValue s).
  (* Delay with the default signal as its reset value *)
  Definition DelayCE {t}
    : Circuit (signal t * signal Bit) (signal t) :=
    DelayInitCE (defaultCombValue t).

  (* Loop with the default signal as its reset value and no enable *)
  Definition Loop {i o s}
             (body : Circuit (i * signal s) (o * signal s))
    : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true))) (LoopInitCE (defaultCombValue s) body).
  (* Delay with the default signal as its reset value and no enable *)
  Definition Delay {t} : Circuit (signal t) (signal t) :=
    Compose (Comb (fun i => ret (i, constant true))) (DelayInitCE (defaultCombValue t)).
End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
