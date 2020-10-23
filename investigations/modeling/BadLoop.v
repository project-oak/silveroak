
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

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.
Open Scope monad_scope.

Open Scope type_scope.

Generalizable All Variables.

(* Haskell code from https://github.com/project-oak/oak-hardware/blob/main/investigations/lava/Lava.hs:

loopMF' :: MonadFix m => ((a, c) -> m (b, c)) -> a -> m (b, c)
loopMF' circuit a
  = mfix (\bc -> do (b, c') <- circuit (a, snd bc)
                    return (b, c'))
*)


(* Bad attempt at implementing the Haskell loop combinator in Coq
   which is specialized to a feedback wire of type bool and also
   uses a default feedback value of [false] which is probably bogus
   but is there as a workaround for not having lazy evaluation.
*)
Definition loop `{Monad m} `{MonadFix m} {A B}
           (circuit : (A * list bool) -> m (B * list bool)) (a:A) : m B :=
  '(b, _) <- mfix (fun f bc => '(b, c') <- circuit (a, snd bc) ;;
                               ret (b, c')
                  ) (a, [false]) ;;
  ret b.

Definition nand2 (ab : list bool * list bool) : ident (list bool) :=
  ret (map (fun '(a,b) => a && b) (combine (fst ab) (snd ab))).

Definition fork2 {A} (a:A)  : ident (A * A) := ret (a, a).

(* loopedNAND also causes Coq to go into an infinite loop. *)

Definition delayBit (input: list bool) : ident (list bool) :=
  ret (false :: input).

(* The loopedNAND definition below gives the error:
Unable to satisfy the following constraints:
In environment:
a : list bool

?H0 : "MonadFix ident"
Not in proof mode.

because there is no MonadFix instance for the identity monad.
Perhaps the best way forward is to make a list monad and define
MonadFix for that?
*)

Definition loopedNAND (a : list bool) : ident (list bool) :=
  loop (nand2 >=> delayBit >=> fork2) a.