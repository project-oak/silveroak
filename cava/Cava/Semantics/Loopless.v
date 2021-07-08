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
  | Par f g => loops_state f * loops_state g
  | Compose f g => loops_state f * loops_state g
  | @DelayInit _ _ t _ => tzero
  | @LoopInitCE _ _ _ _ t _ body => loops_state body * t
  end.

Fixpoint loops_reset_state {i o} (c : Circuit i o)
  : value (signal:=combType) (loops_state c) :=
  match c with
  | Comb _ => tt
  | Par f g => (loops_reset_state f, loops_reset_state g)
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
  | Par f g =>
    Comb (i:=(_*_*(_*_))) (o:=_*_*(_*_))
         (fun '(x1,x2,(st1,st2)) => (x1,st1,(x2,st2))) (* rearrange *)
         >==> Par (loopless f) (loopless g) (* recursive call *)
         >==> (Comb (i:=(_*_*(_*_))) (o:=_*_*(_*_))
                    (fun '(y1,st1,(y2,st2)) => (y1,y2,(st1,st2)))) (* rearrange *)
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
