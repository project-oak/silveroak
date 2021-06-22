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
Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Import ListNotations VectorNotations MonadNotation.

Require Import Cava.Core.CavaClass.
Require Import Cava.Core.Signal.

(******************************************************************************)
(* Inductive to capture circuit's sequential structure                        *)
(******************************************************************************)

Section WithCava.
  Context `{semantics:Cava}.

  Inductive Circuit : type -> type -> Type :=
  | Comb : forall {i o}, (value i -> cava (value o)) -> Circuit i o
  | Compose : forall {i t o}, Circuit i t -> Circuit t o -> Circuit i o
  | First : forall {i o t}, Circuit i o -> Circuit (i * t) (o * t)
  | Second : forall {i o t}, Circuit i o -> Circuit (t * i) (t * o)
  | LoopInitCE :
      forall {i o : type} {s : SignalType} (resetval : combType s),
        Circuit (i * s) (o * s) -> Circuit (i * Bit) o
  | DelayInitCE : forall {t} (resetval : combType t), Circuit (t * Bit) t
  .

  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : type :=
    match c with
    | Comb _ => tzero
    | Compose f g => circuit_state f * circuit_state g
    | First f => circuit_state f
    | Second f => circuit_state f
    | @LoopInitCE i o s _ f => circuit_state f * s
    | @DelayInitCE t _ => t
    end.

  (* The state of the circuit after a reset *)
  Fixpoint reset_state {i o} (c : Circuit i o)
    : value (signal:=combType) (circuit_state c) :=
    match c as c return value (circuit_state c) with
    | Comb _ => tt
    | Compose f g => (reset_state f, reset_state g)
    | First f => reset_state f
    | Second f => reset_state f
    | LoopInitCE resetval f => (reset_state f, resetval)
    | DelayInitCE resetval => resetval
    end.

  (* Loop with no enable; set enable to always be true *)
  Definition LoopInit {i o s} (resetval : combType s)
             (body : Circuit (i * s) (o * s))
    : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true)))
            (LoopInitCE resetval body).
  (* Delay with no enable; set enable to always be true *)
  Definition DelayInit {t} (resetval : combType t)
    : Circuit t t :=
    Compose (Comb (fun i => ret (i, constant true))) (DelayInitCE resetval).

  (* Loop with the default signal as its reset value *)
  Definition LoopCE {i o} {s : SignalType}
    : Circuit (i * s) (o * s) -> Circuit (i * Bit) o :=
    LoopInitCE (defaultCombValue s).
  (* Delay with the default signal as its reset value *)
  Definition DelayCE {t : SignalType} : Circuit (t * Bit) t :=
    DelayInitCE (defaultCombValue t).

  (* Loop with the default signal as its reset value and no enable *)
  Definition Loop {i o} {s : SignalType} (body : Circuit (i * s) (o * s))
    : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true))) (LoopInitCE (defaultCombValue s) body).
  (* Delay with the default signal as its reset value and no enable *)
  Definition Delay {t : SignalType} : Circuit t t :=
    Compose (Comb (fun i => ret (i, constant true))) (DelayInitCE (defaultCombValue t)).

End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
