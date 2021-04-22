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

Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint curried (l: list Type) ret: Type :=
  match l with
  | [] => ret
  | x::xs => x -> curried xs ret
  end.

Fixpoint tupled (l: list Type) prefix: Type :=
  match l with
  | [] => prefix
  | x::xs => tupled xs (prefix * x)%type
  end.

Definition tupled' (l: list Type): Type :=
  match l with
  | [] => unit
  | x::xs => tupled xs x
  end.

Fixpoint tupledR (l : list Type) : Type :=
  match l with
  | [] => unit
  | x :: xs => x * tupledR xs
  end.

Definition uncurriedR (l: list Type) ret: Type :=
  tupledR l -> ret.

Definition uncurried (l: list Type) ret: Type :=
  tupled' l -> ret.

Fixpoint unbalance (ts: list Type) {accumT : Type}
  : tupled ts accumT -> accumT * tupledR ts :=
  match ts with
  | [] => fun acc => (acc, tt)
  | x::xs => fun ab =>
      let '(acc, vx, vxs) := unbalance xs ab in
      (acc, (vx, vxs))
  end.

Definition unbalance' (ts : list Type)
                     : tupled' ts -> tupledR ts :=
  match ts with
  | [] => fun _ => tt
  | x::xs => unbalance xs
  end.

Fixpoint rebalance (ts : list Type) {accumT : Type} (accum : accumT)
  : tupledR ts -> tupled ts accumT :=
  match ts with
  | [] => fun _ : unit => accum
  | x::xs =>
    fun ab => rebalance xs (accum, fst ab) (snd ab)
  end.

Definition rebalance' (ts : list Type)
  : tupledR ts -> tupled' ts :=
  match ts with
  | [] => fun _ => tt
  | x::xs => fun ab => rebalance xs (fst ab) (snd ab)
  end.

Fixpoint curry (l : list Type) ret {struct l}: uncurriedR l ret -> curried l ret :=
  match l with
  | [] => fun f => f tt
  | X :: XS => fun f x =>
      curry XS ret (fun txs => f (x, txs))
  end.

Fixpoint curry_helper l ret {struct l}: (tupled' l -> ret) -> uncurriedR l ret :=
  match l with
  | [] => fun f => f
  | X::XS => fun f '(y,ys) => f (rebalance XS y ys)
  end.

Fixpoint uncurry (l : list Type) ret {struct l}: curried l ret -> uncurriedR l ret :=
  match l with
  | [] => fun f _ => f
  | X :: XS => fun f '(y,ys) => uncurry XS ret (f y) ys
  end.

Definition uncurriedR_to_uncurried l ret (f: uncurriedR l ret): uncurried l ret :=
  fun x => f (unbalance' l x).

Definition uncurried_to_uncurriedR l ret: uncurried l ret -> uncurriedR l ret :=
  match l with
  | [] => fun f _ => f tt
  | X::XS => fun f '((x,xs):tupledR (X::XS)) => f (rebalance XS x xs)
  end.

