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

Definition uncurried' (l: list Type) ret: Type :=
  tupledR l -> ret.
  (* match l with *)
  (* | [] => ret *)
  (* | x::xs => uncurried xs x ret *)
  (* end. *)

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

Fixpoint curry (l : list Type) ret {struct l}: uncurried' l ret -> curried l ret :=
  match l with
  | [] => fun f => f tt
  | X :: XS => fun f x =>
      curry XS ret (fun txs => f (x, txs))
  end.

Fixpoint curry_helper l ret {struct l}: (tupled' l -> ret) -> uncurried' l ret :=
  match l with
  | [] => fun f => f
  | X::XS => fun f '(y,ys) => f (rebalance XS y ys)
  end.

Fixpoint uncurry (l : list Type) ret {struct l}: curried l ret -> uncurried' l ret :=
  match l with
  | [] => fun f _ => f
  | X :: XS => fun f '(y,ys) => uncurry XS ret (f y) ys
  end.



(*     (1* forall prefix : Type, prefix -> curried l (tupled l prefix) := *1) *)

(* Fixpoint curry_helper (l : list Type): *)
(*     forall prefix : Type, prefix -> curried l (tupled l prefix) := *)
(*   match l with *)
(*   | [] => fun _ x => x *)
(*   | X :: XS => *)
(*       fun prefix (p: prefix) (x: X) => *)
(*       curry_helper _ (prefix * X)%type (p, x) *)
(*   end. *)

(* Fixpoint curry_helper2 {o} (l : list Type): *)
(*   forall prefix, (tupled l prefix -> o) -> curried l (tupled l prefix) -> curried l o := *)
(*   match l with *)
(*   | [] => fun prefix f (x : curried [] (tupled [] prefix)) => f x *)
(*   | X :: XS => fun prefix f x y => *)
(*     curry_helper2 XS (prefix * X)%type f (x y) *)
(*   end. *)

(* (1* Fixpoint uncurried_apply (l : list Type) (ret : Type): *1) *)
(* (1*   forall prefix, tupled l prefix -> uncurried l prefix ret -> ret := *1) *)
(* (1*   match l with *1) *)
(* (1*   | [] => fun _ args f => f args *1) *)
(* (1*   | X :: XS => fun prefix args f => *1) *)
(* (1*     uncurried_apply XS ret (prefix * X) args f *1) *)
(* (1*   end. *1) *)

(* (1* Definition curry (l : list Type) ret: uncurried' l ret -> curried l ret := *1) *)
(* (1*   match l with *1) *)
(* (1*   | [] => fun x => x *1) *)
(* (1*   | X::XS => fun f x => curry_helper2 _ X (fun y => uncurried_apply _ ret X y f) (curry_helper _ X x) *1) *)
(* (1*   end. *1) *)

(* (1* Fixpoint uncurried_helper (l : list Type) (ret : Type): *1) *)
(* (1*   forall prefix, (tupled l prefix -> ret) -> uncurried l prefix ret := *1) *)
(* (1*   match l with *1) *)
(* (1*   | [] => fun _ f => f *1) *)
(* (1*   | X :: XS => fun prefix f => uncurried_helper XS ret (prefix * X)%type f *1) *)
(* (1*   end. *1) *)

(* (1* Definition uncurried_helper' l ret: (tupled' l -> ret) -> uncurried' l ret := *1) *)
(* (1*   match l with *1) *)
(* (1*   | [] => fun f => f tt *1) *)
(* (1*   | X::XS => fun f => uncurried_helper XS ret X f *1) *)
(* (1*   end. *1) *)


(* (1* Fixpoint curried_apply (l : list Type) (ret : Type) {struct l}: *1) *)
(* (1*   forall p, tupledR p -> curried l ret -> ret. *1) *)
(* (1* destruct l; intros. *1) *)
(* (1* exact X0. *1) *)
(* (1* eapply curried_apply. *1) *)
(* (1* apply X. *1) *)
(* (1* apply X0. *1) *)
(* (1* Defined. *1) *)



(* (1* exact X0. *1) *)

(* (1* eapply curried_apply. *1) *)
(* (1* apply X. *1) *)
(* (1* apply X. *1) *)
(* (1* apply X0. *1) *)
(* (1* destruct l. *1) *)

(* (1*   match l *1) *)
(* (1*   as l return *1) *)
(* (1*   forall prefix, tupled l prefix -> curried l ret -> ret *1) *)
(* (1*   with *1) *)
(* (1*   | [] => fun _ args f => f *1) *)
(* (1*   | X :: XS => fun prefix '((y,ys) : tupled (X :: XS) _) f => *1) *)
(* (1*     curried_apply XS ret (prefix * X) ys (f y) *1) *)
(* (1*   end. *1) *)
