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
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

From Cava Require Import Acorn.Acorn.

Definition halfAdder {m signal} `{Cava m signal}
                     (ab : signal BitType * signal BitType)
                     : m (signal BitType * signal BitType) :=
  let (a, b) := ab in 
  partial_sum <- xor2 (a, b) ;;
  carry <- and2 (a, b) ;;
  ret (partial_sum, carry).

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour : forall (a : bool) (b : bool),
                            unIdent (halfAdder (a, b)) = (xorb a b, a && b).

Proof.
  auto.
Qed.

Definition halfAdderAlt {m signal} `{Cava m signal}
                        (ab : signal (PairType BitType BitType))
                        : m (signal (PairType BitType BitType)) :=
  let (a, b) := unpair ab in 
  partial_sum <- xor2 (a, b) ;;
  carry <- and2 (a, b) ;;
  ret (pair partial_sum carry).

Definition fullAdder {m signal} `{Cava m signal}
                     '(cin, (a, b))
                     : m (signal BitType * signal BitType) :=
  '(abl, abh) <- halfAdder (a, b) ;;
  '(abcl, abch) <- halfAdder (abl, cin) ;;
  cout <- or2 (abh, abch) ;;
  ret (abcl, cout).

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                            combinational (fullAdder (cin, (a, b)))
                              = (xorb cin (xorb a b),
                                 (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

Definition fullAdderAlt {m signal} `{Cava m signal}
                        (cinab : signal (PairType BitType (PairType BitType BitType)))
                       : m (signal (PairType BitType BitType)) :=
  let (cin, ab) := unpair cinab in
  let (a, b) := unpair ab in
  abl_abh <- halfAdderAlt ab ;;
  let (abl, abh) := unpair abl_abh in
  abcl_abch <- halfAdderAlt (pair abl cin) ;;
  let (abcl, abch) := unpair abcl_abch in
  cout <- or2 (abh, abch) ;;
  ret (pair abcl cout).

Definition fullAdderAlt2 {m signal} `{Cava m signal}
                        (cinab : signal BitType * signal (PairType BitType BitType))
                       : m (signal BitType * signal BitType) :=
  let (cin, ab) := cinab in
  let (a, b) := unpair ab in
  abl_abh <- halfAdderAlt ab ;;
  let (abl, abh) := unpair abl_abh in
  abcl_abch <- halfAdderAlt (pair abl cin) ;;
  let (abcl, abch) := unpair abcl_abch in
  cout <- or2 (abh, abch) ;;
  ret (abcl, cout).