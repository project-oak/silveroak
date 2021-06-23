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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.Multiplexers.
Import ListNotations Circuit.Notations.

Section WithCava.
  Context `{semantics : Cava}.

  (* make a circuit with one delay for each signal, given reset values *)
  Fixpoint delays {t : type} : value (signal:=combType) t -> Circuit t t :=
    match t with
    | tzero => fun _ => Id
    | tone t => DelayInit
    | tpair t1 t2 => fun v => Par (delays (fst v)) (delays (snd v))
    end.

  (* get the value stored in the 1-delay circuit *)
  Fixpoint delays_get {t : type}
    : forall {v : value t}, value (circuit_state (delays v)) -> value t :=
    match t with
    | tzero => fun _ _ => tt
    | tone _ => fun _ => snd
    | tpair _ _ => fun _ st => (delays_get (fst st), delays_get (snd st))
    end.

  (* make a circuit with repeated delays for each signal *)
  Fixpoint ndelays {t : type} (v : list (value (signal:=combType) t)) : Circuit t t :=
    match v with
    | [] => Id
    | v0 :: v => ndelays v >==> delays v0
    end.

  (* get all the values stored in the n-delay circuit *)
  Fixpoint ndelays_get {t v} : value (circuit_state (@ndelays t v)) -> list (value t) :=
    match v with
    | [] => fun _ => []
    | _ :: _ => fun st => delays_get (snd st) :: ndelays_get (fst st)
    end.

End WithCava.

Inductive is_delays : forall {t}, Circuit t t -> Prop :=
| is_delays_delay : forall t resetval, is_delays (DelayInit (t:=t) resetval)
| is_delays_par :
    forall t1 t2 c1 c2,
      is_delays c1 -> is_delays c2 ->
      @is_delays (t1 * t2) (Par c1 c2)
.

Inductive is_ndelays : forall {t}, nat -> Circuit t t -> Prop :=
| is_ndelays_id : forall t, is_ndelays (t:=t) 0 Id
| is_ndelays_compose :
    forall t n c1 c2,
      is_ndelays (t:=t) n c1 -> is_delays c2 ->
      is_ndelays (S n) (c1 >==> c2)
.

Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists delay_circuit,
    is_ndelays n delay_circuit
    /\ cequiv c1 (delay_circuit >==> c2).

Fixpoint loops_state {i o} (c : Circuit i o) : type :=
  match c with
  | Comb _ => tzero
  | First f => loops_state f
  | Second f => loops_state f
  | Compose f g => loops_state f * loops_state g
  | @DelayInitCE _ _ t _ => tzero
  | @LoopInitCE _ _ _ _ t _ body => loops_state body * t
  end.

Fixpoint loops_reset_state {i o} (c : Circuit i o)
  : value (signal:=combType) (loops_state c) :=
  match c with
  | Comb _ => tt
  | First f => loops_reset_state f
  | Second f => loops_reset_state f
  | Compose f g => (loops_reset_state f, loops_reset_state g)
  | DelayInitCE _=> tt
  | LoopInitCE resetval body => (loops_reset_state body, resetval)
  end.

Require Import ExtLib.Structures.Monad.
Import MonadNotation.

(* Pull the loops out of the circuit completely *)
Fixpoint loopless {i o} (c : Circuit i o)
  : Circuit (i * loops_state c) (o * loops_state c) :=
  match c as c in Circuit i o
        return Circuit (i * loops_state c) (o * loops_state c) with
  | Comb f => First (Comb f)
  | First f =>
    Comb (i:=(_*_*_)) (fun '(x1,x2,st) => ret (x1,st,x2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> Comb (i:=(_*_*_)) (fun '(y1,st,y2) => ret (y1,y2,st)) (* rearrange *)
  | Second f =>
    Comb (i:=(_*_*_)) (fun '(x1,x2,st) => ret (x1,(x2,st))) (* rearrange *)
         >==> Second (loopless f) (* recursive call *)
         >==> Comb (i:=(_*(_*_))) (fun '(y1,(y2,st)) => ret (y1,y2,st)) (* rearrange *)
  | Compose f g =>
    Comb (i:=(_*(_*_))) (fun '(x,(st1,st2)) => ret (x,st1,st2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> Comb (i:=(_*_*_)) (fun '(y,st1,st2) => ret (y,st2,st1)) (* rearrange *)
         >==> First (loopless g) (* recursive call *)
         >==> Comb (i:=(_*_*_))  (fun '(z,st2,st1) => ret (z,(st1,st2))) (* rearrange *)
  | DelayInitCE resetval => First (DelayInitCE resetval)
  | @LoopInitCE _ _ _ _ s resetval body =>
    (Comb (i:=(_*_*(_*_)))
          (fun '(x,en,(body_st, loop_st)) =>
             ret (en,loop_st,(x,loop_st,body_st)))) (* rearrange *)
         >==> Second (loopless body) (* recursive call *)
         >==> (Comb (i:=(Bit * _ * (_ * _ * _))) (o:=(_*(_* _)))
                    (fun '(en, loop_st, (y, loop_st', body_st')) =>
                       loop_st' <- mux2 en (loop_st,loop_st') ;;
                       ret (y,(body_st',loop_st'))))
  end.

Definition phase_retimed {i o} (n m : nat) (c1 c2 : Circuit i o) : Prop :=
  exists state_resets input_resets,
    length state_resets = n
    /\ length input_resets = m
    /\ cequiv c1 (LoopInit (loops_reset_state c2)
                          (Par (ndelays input_resets) (ndelays state_resets)
                           >==> loopless c2)).
