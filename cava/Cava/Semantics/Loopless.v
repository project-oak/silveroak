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

Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Import Circuit.Notations MonadNotation.

Fixpoint loops_state {i o} (c : Circuit i o) : type :=
  match c with
  | Comb _ => tzero
  | First f => loops_state f
  | Second f => loops_state f
  | Compose f g => loops_state f * loops_state g
  | @DelayInit _ _ t _ => tzero
  | @LoopInitCE _ _ _ _ t _ body => loops_state body * t
  end.

Fixpoint loops_reset_state {i o} (c : Circuit i o)
  : value (signal:=combType) (loops_state c) :=
  match c with
  | Comb _ => tt
  | First f => loops_reset_state f
  | Second f => loops_reset_state f
  | Compose f g => (loops_reset_state f, loops_reset_state g)
  | DelayInit _=> tt
  | LoopInitCE resetval body => (loops_reset_state body, resetval)
  end.

(* Pull the loops out of the circuit completely *)
Fixpoint loopless {i o} (c : Circuit i o)
  : Circuit (i * loops_state c) (o * loops_state c) :=
  match c as c in Circuit i o
        return Circuit (i * loops_state c) (o * loops_state c) with
  | Comb f => First (Comb f)
  | Compose f g =>
    Comb (i:=_*(_*_)) (o:=_*_*_)
         (fun '(x,(st1,st2)) => (x,st1,st2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> (Comb (i:=(_*_*_)) (o:=_*_*_)
                    (fun '(y,st1,st2) => (y,st2,st1))) (* rearrange *)
         >==> First (loopless g) (* recursive call *)
         >==> (Comb (i:=(_*_*_)) (o:=_*(_*_))
                    (fun '(z,st2,st1) => (z,(st1,st2)))) (* rearrange *)
  | First f =>
    Comb (i:=(_*_*_)) (o:=_*_*_)
         (fun '(x1,x2,st) => (x1,st,x2)) (* rearrange *)
         >==> First (loopless f) (* recursive call *)
         >==> (Comb (i:=(_*_*_)) (o:=_*_*_)
                    (fun '(y1,st,y2) => (y1,y2,st))) (* rearrange *)
  | Second f =>
    Comb (i:=(_*_*_)) (o:=_*(_*_))
         (fun '(x1,x2,st) => (x1,(x2,st))) (* rearrange *)
         >==> Second (loopless f) (* recursive call *)
         >==> (Comb (i:=(_*(_*_))) (o:=_*_*_)
                    (fun '(y1,(y2,st)) => (y1,y2,st))) (* rearrange *)
  | DelayInit resetval => First (DelayInit resetval)
  | @LoopInitCE _ _ _ _ s resetval body =>
    (Comb (i:=(_*_*(_*_))) (o:=_*_*(_*_*_))
          (fun '(x,en,(body_st, loop_st)) =>
             (en,loop_st,(x,loop_st,body_st)))) (* rearrange *)
         >==> Second (loopless body) (* recursive call *)
         >==> (Comb (i:=(Bit * _ * (_ * _ * _))) (o:=(_*(_* _)))
                    (fun '(en, loop_st, (y, loop_st', body_st')) =>
                       let loop_st' := if (en : bool) then loop_st' else loop_st in
                       (y,(body_st',loop_st'))))
  end.

Fixpoint to_loops_state {i o} {c : Circuit i o} {struct c}
  : value (circuit_state c) -> value (loops_state c) :=
  match c with
  | Comb _ => fun _ => tt
  | Compose _ _ => fun x => (to_loops_state (fst x), to_loops_state (snd x))
  | First f => to_loops_state (c:=f)
  | Second f => to_loops_state (c:=f)
  | DelayInit _ => fun _ => tt
  | LoopInitCE _ body => fun x => (to_loops_state (fst x), snd x)
  end.

Fixpoint to_loopless_state {i o} {c : Circuit i o}
  : value (circuit_state c) -> value (circuit_state (loopless c)) :=
  match c with
  | Comb _ => fun _ => tt
  | Compose f g =>
    fun x => (tt, to_loopless_state (fst x), tt, to_loopless_state (snd x), tt)
  | First f =>
    fun x => (tt, to_loopless_state (c:=f) x, tt)
  | Second f =>
    fun x => (tt, to_loopless_state (c:=f) x, tt)
  | DelayInit _ => fun x => x
  | LoopInitCE _ body =>
    fun x => (tt, to_loopless_state (fst x), tt)
  end.

Fixpoint reassemble {i o} {c : Circuit i o}
  : value (loops_state c) -> value (circuit_state (loopless c))
    -> value (circuit_state c) :=
  match c with
  | Comb _ => fun _ _ => tt
  | Compose f g => fun (x : value (loops_state f) * value (loops_state g))
                    (y : unit * value (circuit_state (loopless f)) * unit
                         * value (circuit_state (loopless g)) * unit) =>
                     (reassemble (fst x) (snd (fst (fst (fst y)))),
                      reassemble (snd x) (snd (fst y)))
  | First f => fun (x : value (loops_state f))
                (y : unit * value (circuit_state (loopless f)) * unit) =>
                reassemble x (snd (fst y))
  | Second f => fun (x : value (loops_state f))
                 (y : unit * value (circuit_state (loopless f)) * unit) =>
                reassemble x (snd (fst y))
  | DelayInit _ => fun x y => y
  | @LoopInitCE _ _ _ _ t _ body => fun (x : value (loops_state body) * value t)
                                     (y : unit * value (circuit_state (loopless body)) * unit) =>
                                     (reassemble (fst x) (snd (fst y)), snd x)
  end.
