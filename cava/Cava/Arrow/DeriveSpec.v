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

Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Arrow.ArrowExport.

(* This file contains tactics and notations designed to simplify proofs that
   derive or prove specifications for kappa-level circuits. *)

Ltac kappa_spec_begin :=
  intros; cbn [interp_combinational'];
  repeat match goal with
         | |- context [primitive_interp ?p] =>
           let x := constr:(primitive_interp p) in
           let y := (eval cbv [primitive_interp] in x) in
           progress change x with y
         | _ => progress cbn [denote_kind primitive_input primitive_output]
         end; fold denote_kind in *.

Create HintDb kappa_interp discriminated.

Ltac kappa_spec_step :=
  match goal with
  | _ => progress autorewrite with kappa_interp
  | H : context [interp_combinational' (_ coq_func) _ = _] |- _ => rewrite H by eauto
  | |- context [interp_combinational'] => kappa_spec_begin
  end.
Ltac kappa_spec := kappa_spec_begin; repeat kappa_spec_step.

Ltac derive_spec_done :=
  lazymatch goal with
  | |- context [interp_combinational' ?x] =>
    fail "derived spec still contains disallowed term: interp_combinational'" x
  | _ => idtac
  end;
  repeat match goal with
         | x := _ |- _ => subst x
         end;
  (instantiate_app_by_reflexivity || reflexivity).
Ltac derive_spec_simplify :=
  repeat match goal with
         | |- context [let '(x, _) := ?p in x] =>
           change (let '(x, _) := p in x) with (fst p)
         | |- context [let '(_, x) := ?p in x] =>
           change (let '(_, x) := p in x) with (snd p)
         end.
Ltac derive_spec :=
  match goal with
  | |- context [interp_combinational'] => idtac
  | |- ?x => fail "goal does not include interp_combinational:" x
  end;
  intros; derive_spec_simplify; kappa_spec; derive_spec_done.

Ltac derive_map_spec :=
  match goal with
  | |- context [Vector.map ?f] =>
    match f with
    | context [interp_combinational'] => idtac
    end;
    match type of f with
    | ?t =>
      let g := fresh "g" in
      evar (g:t);
      erewrite (Vector.map_ext _ _ f g) by derive_spec
    end
  end.

Ltac derive_foldl_spec :=
  match goal with
  | |- context [Vector.fold_left ?f] =>
    match f with
    | context [interp_combinational'] => idtac
    end;
    match type of f with
    | ?t =>
      let g := fresh "g" in
      evar (g:t);
      erewrite (fold_left_ext f g) by derive_spec
    end
  end.

(* convenient notation *)
Notation kinterp x := (interp_combinational' (x coq_func)).

