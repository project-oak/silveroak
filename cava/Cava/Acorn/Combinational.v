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

Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.

Require Import Cava.Acorn.AcornSignal.
Require Import Cava.Acorn.AcornCavaClass.

Fixpoint denoteCombinaional (t : SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt s => Vector.t (denoteCombinaional vt) s
  | ExternalType _ => string
  | Pair A B => denoteCombinaional A * denoteCombinaional B
  end.

Instance Combinational : Cava denoteCombinaional :=
{ m := ident;
  one := true;
  zero := false;
  inv i := ret (negb i);
  and2 '(i0, i1) := ret (i0 && i1);
  or2 '(i0, i1) := ret (i0 || i1);
  xor2 '(i0, i1) := ret (xorb i0 i1);
  pair _ _ a b := (a, b);
  fsT _ _ '(a, b) := a;
  snD _ _ '(a, b) := b;
  peel _ _ v := v;
  unpeel _ _ v := v;
}.

Definition combinational {a} (circuit : ident a) : a := unIdent circuit.
