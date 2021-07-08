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
  | Par : forall {i1 i2 o1 o2}, Circuit i1 o1 -> Circuit i2 o2 -> Circuit (i1 * i2) (o1 * o2)
  | LoopInitCE :
      forall {i o s : type} (resetval : value (signal:=combType) s),
        Circuit (i * s) (o * s) -> Circuit (i * Bit) o
  | DelayInit : forall {t} (resetval : value (signal:=combType) t), Circuit t t
  .

  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : type :=
    match c with
    | Comb _ => tzero
    | Compose f g => circuit_state f * circuit_state g
    | Par f g => circuit_state f * circuit_state g
    | @LoopInitCE i o s _ f => circuit_state f * s
    | @DelayInit t _ => t
    end.

  (* The state of the circuit after a reset *)
  Fixpoint reset_state {i o} (c : Circuit i o)
    : value (signal:=combType) (circuit_state c) :=
    match c as c return value (circuit_state c) with
    | Comb _ => tt
    | Compose f g => (reset_state f, reset_state g)
    | Par f g => (reset_state f, reset_state g)
    | LoopInitCE resetval f => (reset_state f, resetval)
    | DelayInit resetval => resetval
    end.

  (* Loop with no enable; set enable to always be true *)
  Definition LoopInit {i o s} (resetval : value (signal:=combType) s)
             (body : Circuit (i * s) (o * s))
    : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true)))
            (LoopInitCE resetval body).

  (* Delay with an enable *)
  Definition DelayInitCE {t} (resetval : value (signal:=combType) t)
    : Circuit (t * Bit) t :=
    LoopInitCE resetval (Comb (i:=t*t) (fun '(i, s) => ret (s, i))).

  (* Loop with the default signal as its reset value *)
  Definition LoopCE {i o s}
    : Circuit (i * s) (o * s) -> Circuit (i * Bit) o :=
    LoopInitCE (default_value defaultCombValue s).
  (* Delay with the default signal as its reset value *)
  Definition DelayCE {t} : Circuit (t * Bit) t :=
    DelayInitCE (default_value defaultCombValue t).

  (* Loop with the default signal as its reset value and no enable *)
  Definition Loop {i o s} (body : Circuit (i * s) (o * s)) : Circuit i o :=
    Compose (Comb (fun i => ret (i, constant true)))
            (LoopInitCE (default_value defaultCombValue s) body).
  (* Delay with the default signal as its reset value and no enable *)
  Definition Delay {t} : Circuit t t := DelayInit (default_value defaultCombValue t).

  Definition Id {t} : Circuit t t := Comb ret.
  Definition First {i o t} (f : Circuit i o) : Circuit (i * t) (o * t) := Par f Id.
  Definition Second {i o t} (f : Circuit i o) : Circuit (t * i) (t * o) := Par Id f.

End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
