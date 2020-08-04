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

From Arrow Require Import Category Arrow Kappa Equiv ClosureConversion.
From Cava Require Import Arrow.CavaArrow.
From Cava Require Arrow.CombinationalArrow.

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Open Scope category_scope.
Open Scope arrow_scope.

Notation CavaExpr var := (kappa var).

Section combinational_semantics.
  Import Arrow.CombinationalArrow.
  
  Definition coq_func i o := denote_kind i -> denote_kind o.

  Fixpoint interp_combinational {i o: Kind}
    (expr: kappa (arrow:=Combinational) coq_func i o)
    : denote_kind i -> option (denote_kind o) :=
    match expr with
    | Var x => fun v => Some (x v) 
    | Abs f => fun '(x,y) => interp_combinational (f (fun _ => x)) y
    | App f e => fun y => 
      match (interp_combinational e) tt with
      | Some x => (interp_combinational f) (x, y)
      | None => None
      end
    | Comp g f => (interp_combinational f) >==> (interp_combinational g)
    | Morph m => m
    | Let v f => fun y => 
      match (interp_combinational v) tt with
      | Some x => (interp_combinational (f (fun _ => x))) y
      | None => None
      end
    | LetRec v f => fun _ => None
    end.

    Axiom expression_evaluation_is_arrow_evaluation: forall i o (expr: Kappa i o), forall (x: denote_kind i),
      Closure_conversion (arrow:=Combinational) expr x =
      interp_combinational (expr _) x.

End combinational_semantics.