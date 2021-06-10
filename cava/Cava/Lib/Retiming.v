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

(* Define a restricted type format for the delay circuits to work with *)
Section WithCava.
  Context `{semantics : Cava}.
  (* gives the shape of a collection of signals *)
  Inductive itype : Type :=
  | ione (t : SignalType)
  | ipair (i1 i2 : itype)
  .
  Scheme Equality for itype.

  (* gives the Gallina tuple for the collection of signals specified *)
  Fixpoint ivalue (i : itype) : Type :=
    match i with
    | ione t => signal t
    | ipair a b => ivalue a * ivalue b
    end.

  Fixpoint idefault (i : itype) : ivalue i :=
    match i with
    | ione t => defaultSignal
    | ipair a b => (idefault a, idefault b)
    end.
End WithCava.

Section WithCava.
  Context `{semantics : Cava}.

  (* make a circuit with one delay for each signal, given the delays' reset
     values *)
  Fixpoint delays (t : itype) : Circuit (ivalue t) (ivalue t) :=
    match t with
    | ione t => Delay (t:=t)
    | ipair a b => Par (delays a) (delays b)
    end.

  (* get the value stored in the 1-delay circuit *)
  Fixpoint delays_get {t : itype}
    : circuit_state (delays t) -> ivalue t :=
    match t with
    | ione _ => snd
    | ipair _ _ => fun st => (delays_get (fst st), delays_get (snd st))
    end.

  (* make a circuit with repeated delays for each signal, given the delays'
     reset values for each layer *)
  Fixpoint ndelays (n : nat) (t : itype) : Circuit (ivalue t) (ivalue t) :=
    match n with
    | 0 => Id
    | S m => ndelays m t >==> delays t
    end.

  (* get all the values stored in the n-delay circuit *)
  Fixpoint ndelays_get {n t} : circuit_state (ndelays n t) -> list (ivalue t) :=
    match n with
    | 0 => fun _ => []
    | S _ => fun st => delays_get (snd st) :: ndelays_get (fst st)
    end.
End WithCava.

(* it's possible to define is_delays directly without using itype, but then
   inversion can't handle the type mismatches if the types are not just plain
   identifiers, and you get nonsensical cases where e.g. unit = t1 * t2 *)
Inductive is_delays' : forall t, Circuit (ivalue t) (ivalue t) -> Prop :=
| is_delays'_delay : forall t resetval, is_delays' (ione t) (DelayInit (t:=t) resetval)
| is_delays'_par :
    forall t1 t2 c1 c2,
      is_delays' t1 c1 -> is_delays' t2 c2 ->
      is_delays' (ipair t1 t2) (Par c1 c2)
.
Inductive is_delays : forall {t}, Circuit t t -> Prop :=
| is_delays_is_delays' : forall t c, is_delays' t c -> is_delays c
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

Definition mealy {i o} (c : Circuit i o)
  : Circuit (i * circuit_state c) (o * circuit_state c) :=
  Comb (fun '(input, st) =>
          let st_out := step c st input in
          (snd st_out, fst st_out)).

(* we don't really want *full* mealy; just for loops -- and this state can be itype!! *)

Fixpoint loops_state {i o} (c : Circuit i o) : itype :=
  match c with
  | Comb _ => ione Void
  | First f => loops_state f
  | Second f => loops_state f
  | Compose f g => ipair (loops_state f) (loops_state g)
  | @DelayInitCE _ _ t _ => ione Void
  | @LoopInitCE _ _ _ _ t _ body => ipair (loops_state body) (ione t)
  end.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.

(* Pull the loops out of the circuit completely *)
(* TODO: ask Ben B to remind me whose idea this was so they can be credited here *)
Fixpoint loopless {i o} (c : Circuit i o)
  : Circuit (i * ivalue (loops_state c)) (o * ivalue (loops_state c)) :=
  match c as c in Circuit i o
        return Circuit (i * ivalue (loops_state c))
                       (o * ivalue (loops_state c)) with
  | Comb f => First (Comb f)
  | First f =>
    Comb (fun '(x1,x2,st) => ret (x1,st,x2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> Comb (fun '(y1,st,y2) => ret (y1,y2,st)) (* rearrange *)
  | Second f =>
    Comb (fun '(x1,x2,st) => ret (x1,(x2,st))) (* rearrange *)
         >==> Second (loopless f) (* recursive call *)
         >==> Comb (fun '(y1,(y2,st)) => ret (y1,y2,st)) (* rearrange *)
  | Compose f g =>
    Comb (fun '(x,(st1,st2)) => ret (x,st1,st2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> Comb (fun '(y,st1,st2) => ret (y,st2,st1)) (* rearrange *)
         >==> First (loopless g) (* recursive call *)
         >==> Comb (fun '(z,st2,st1) => ret (z,(st1,st2))) (* rearrange *)
  | DelayInitCE resetval => First (DelayInitCE resetval)
  | LoopInitCE resetval body =>
    (* need : i * Bit * (lstate body * t) -> o * (lstate body * t) *)
    (* loopless body : i * t * lstate body -> o * t * lstate body *)
    Comb (fun '(x,en,(body_st, loop_st)) =>
            ret (en,loop_st,(x,loop_st,body_st))) (* rearrange *)
         >==> Second (loopless body) (* recursive call *)
         >==> Comb (fun '(en, loop_st, (y, loop_st', body_st')) =>
                      loop_st' <- mux2 en (loop_st,loop_st') ;;
                      (y,(body_st',loop_st')))
  end.


(* can make a def that re-adds loops only to outside, then prove all circuits
   equivalent to this transformation *)

Definition phase_retimed {i o} (n m : nat) (c1 c2 : Circuit i o) : Prop :=
  exists state_delays input_delays
    (proj : ivalue (loops_state c1) -> ivalue (loops_state c2)),
    is_ndelays n state_delays
    /\ is_ndelays m input_delays
    /\ cequiv (loopless c1 >==> Second (Comb (fun st => ret (proj st))))
             (Par input_delays (Comb (fun st => ret (proj st)) >==> state_delays)
                  >==> loopless c2).
