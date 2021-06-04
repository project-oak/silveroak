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
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Lib.CircuitTransforms.
Import Circuit.Notations.


(*

c1 := c2 >==> Delay

retimed 1 c1 c2

c1 [in0;?;in1;?;in2] = c2 [in0;in1;in2]

Can't step the circuits at the same rate and expect matching output!!
Need to step retimed version and *not* non-retimed!

c1_t=0 : c1 []
c2_t=0 : c2 []

c1_t=1 : c1 [in0]
c2_t=0 : c2 []


 *)

(*
(* The retiming relation is similar to cequiv, except that the relation now
   takes a natural-number argument signifying how many steps remain before the
   output of c1 will match the stored output from c2 *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (R : nat -> o -> circuit_state c1 -> circuit_state c2 -> Prop),
    (* when c1 gets an input, R holds with n steps remaining *)
    (forall st1 st2 input,
        R n (snd (step c2 st2 input)) (fst (step c1 st1 input))
          (fst (step c2 st2 input)))
    (* if R holds for a 0 counter, then output of next step must match stored
       output *)
    /\ (forall st1 st2 input output,
        R 0 output st1 st2 -> snd (step c1 st1 input) = output)
    (* if R holds for a nonzero counter, continue stepping c1 *)
    /\ (forall m st1 st2 input output,
          R (S m) output st1 st2 ->
          m < n ->
          R m output (fst (step c1 st1 input)) st2).

*)
(*
(* The retiming relation is similar to cequiv, except that the relation now
   takes a natural-number argument signifying how many steps remain before the
   outputs will match *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (R : nat -> circuit_state c1 -> circuit_state c2 -> Prop),
    R n (reset_state c1) (reset_state c2)
    /\ (forall m st1 st2 input1 input2,
          R m st1 st2 ->
          m <= n ->
          (* if the inputs match, R holds on the new states with a fresh counter *)
          (input1 = input2 ->
           R n (fst (step c1 st1 input1)) (fst (step c2 st2 input2)))
          (* if the counter is 0, then the outputs match; otherwise R holds on
             the decremented counter *)
          /\ match m with
            | 0 => snd (step c1 st1 input1) = snd (step c2 st2 input2)
            | S m' => R m' (fst (step c1 st1 input1))
                       (fst (step c2 st2 input2))
            end).
*)
(*
(* The retiming relation is similar to cequiv, except that the relation now
   takes a natural-number argument signifying how many steps remain before the
   outputs will match *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (R : nat -> circuit_state c1 -> circuit_state c2 -> Prop),
    (*R n (reset_state c1) (reset_state c2)
    /\ *) (forall l st1 st2 input1 input2,
          (* R holds for each counter in the list *)
          Forall (fun m => R m st1 st2) l ->
          (* list of counters has no duplicates *)
          NoDup l ->
          (* if one of the counters is now 0, outputs must match *)
          (In 0 l -> snd (step c1 st1 input1) = snd (step c2 st2 input2))
          (* R continues to hold on remaining counters *)
          /\ Forall
              (fun m =>
                 R m (fst (step c1 st1 input1)) (fst (step c2 st2 input2)))
              (map Nat.pred (remove Nat.eq_dec 0 l))
          (* if inputs match, then R also holds for a new counter *)
          /\ (input1 = input2 ->
             R n (fst (step c1 st1 input1)) (fst (step c2 st2 input2)))).


(* The retiming relation is similar to cequiv, except that the relation now
   takes a natural-number argument signifying how many steps remain before the
   outputs will match *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (R : list nat -> circuit_state c1 -> circuit_state c2 -> Prop),
    R [] (reset_state c1) (reset_state c2)
    /\ (forall l st1 st2 input1 input2,
          (* R holds *)
          R l st1 st2 ->
          (* no counter is > n *)
          Forall (fun m => m <= n) l ->
          (* list is strongly sorted, no duplicates *)
          (forall i j 0, i < j < length l -> nth i l 0 < nth i j 0) ->
          (* if one of the counters is now 0, outputs must match *)
          (In 0 l -> snd (step c1 st1 input) = snd (step c2 st2 input))
          (* if inputs match, enqueue another counter *)
          (input1 = input2 ->
           R (n :: map Nat.pred (remove 0 l))
             (fst (step c1 st1 input)) (fst (step c2 st2 input)))
          (* if inputs do not match, just *)
          /\ (input1 <> input2 ->
             R
          match m with
          | S m' =>
            (* if there are steps remaining, the outputs might not match;
               decrement steps remaining *)
            R m' (fst (step c1 st1 input))
              (fst (step c2 st2 input))
          | 0 =>
            (* if there are no steps remaining, the output must match and the
               counter resets *)
            snd (step c1 st1 input) = snd (step c2 st2 input)
            /\ R n (fst (step c1 st1 input))
                (fst (step c2 st2 input))
          end).

(* The retiming relation is similar to cequiv, except that the relation now
   takes a natural-number argument signifying how many steps remain before the
   outputs will match *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (R : nat -> circuit_state c1 -> circuit_state c2 -> Prop),
    R n (reset_state c1) (reset_state c2)
    /\ (forall m st1 st2 input1 input2,
          m <= n ->
          R m st1 st2 ->
          match m with
          | S m' =>
            (* if there are steps remaining, the outputs might not match;
               decrement steps remaining *)
            R m' (fst (step c1 st1 input))
              (fst (step c2 st2 input))
          | 0 =>
            (* if there are no steps remaining, the output must match and the
               counter resets *)
            snd (step c1 st1 input) = snd (step c2 st2 input)
            /\ R n (fst (step c1 st1 input))
                (fst (step c2 st2 input))
          end).
 *)

(* Define a restricted type format for the delay circuits to work with *)
Section WithCava.
  Context `{semantics : Cava}.
  (* gives the shape of a collection of signals *)
  Inductive itype : Type :=
  | ione (t : SignalType)
  | ipair (i1 i2 : itype)
  .

  (* gives the Gallina tuple for the collection of signals specified *)
  Fixpoint ivalue (i : itype) : Type :=
    match i with
    | ione t => signal t
    | ipair a b => ivalue a * ivalue b
    end.
End WithCava.

Section WithCava.
  Context `{semantics : Cava}.

  (* make a circuit with one delay for each signal, given the delays' reset
     values *)
  Fixpoint delays (t : itype)
    : ivalue (signal:=combType) t -> Circuit (ivalue t) (ivalue t) :=
    match t with
    | ione t => DelayInit
    | ipair a b =>
      fun resetvals =>
        Par (delays a (fst resetvals)) (delays b (snd resetvals))
    end.

  (* make a circuit with repeated delays for each signal, given the delays'
     reset values for each layer *)
  Definition ndelays (t : itype) (resetvals : list (ivalue (signal:=combType) t))
    : Circuit (ivalue t) (ivalue t) :=
    fold_left (fun c resetvals => c >==> delays t resetvals) resetvals Id.
End WithCava.

Definition retimed {i o} (n : nat) (c1 c2 : Circuit i (ivalue o)) : Prop :=
  exists resetvals,
    length resetvals = n
    /\ cequiv c1 (c2 >==> ndelays o resetvals).
