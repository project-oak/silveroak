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
Require Import Coq.Bool.Bool.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Import ListNotations MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Require Import Cava.ListUtils.
Require Import Cava.Acorn.Acorn.

Section WithCava.
  Context {signal} `{Cava signal}.

  (****************************************************************************)
  (* Build a half-adder                                                       *)
  (****************************************************************************)

  Definition halfAdder '(a, b) :=
    partial_sum <- xor2 (a, b) ;;
    carry <- and2 (a, b) ;;
    ret (partial_sum, carry).

  (****************************************************************************)
  (* Build a full-adder                                                       *)
  (****************************************************************************)
  
  Definition fullAdder '(cin, (a, b))
                       : cava (signal Bit * signal Bit) :=
    '(abl, abh) <- halfAdder (a, b) ;;
    '(abcl, abch) <- halfAdder (abl, cin) ;;
    cout <- or2 (abh, abch) ;;
    ret (abcl, cout).

 End WithCava.
 
Section semantics.

  (* A proof that the half-adder is correct. *)
  Lemma halfAdder_behaviour :
    forall (a : bool) (b : bool),
      unIdent (halfAdder ([a], [b])) = ([xorb a b], [a && b]).
  Proof.
    auto.
  Qed.

  (* A proof that the the full-adder is correct. *)
  Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                              semantics (fullAdder ([cin], ([a], [b])))
                                = ([xorb cin (xorb a b)],
                                  [(a && b) || (b && cin) || (a && cin)]).
  Proof.
    intros.
    unfold semantics.
    unfold fst.
    simpl.
    case a, b, cin.
    all : reflexivity.
  Qed.

End semantics.
