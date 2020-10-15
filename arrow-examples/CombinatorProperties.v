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

From Cava Require Import Arrow.ArrowExport Arrow.CircuitFunctionalEquivalence
     BitArithmetic Tactics VectorUtils.
From ArrowExamples Require Combinators.

(* Functional specifications for circuit combinators *)
Section Specs.
  Fixpoint denote_kind_eqb {A : Kind} : denote_kind A -> denote_kind A -> bool :=
    match A as A0 return denote_kind A0 -> denote_kind A0 -> bool with
    | Unit => fun _ _ => true
    | Bit => Bool.eqb
    | Tuple L R =>
      fun x y => (denote_kind_eqb (fst x) (fst y)
               && denote_kind_eqb (snd x) (snd y))%bool
    | Vector T n =>
      fun x y =>
        let eqb_results := Vector.map2 denote_kind_eqb x y in
        Vector.fold_left andb true eqb_results
    end.

  Fixpoint enable {A : Kind} (en : bool) : denote_kind A -> denote_kind A :=
    match A with
    | Unit => fun x => x
    | Bit => fun x => andb en x
    | Tuple L R => fun x => (enable en (fst x), enable en (snd x))
    | Vector T n => fun x => Vector.map (enable en) x
    end.

  Fixpoint bitwise {A : Kind} (op : bool -> bool -> bool)
    : denote_kind A -> denote_kind A -> denote_kind A :=
    match A as A0 return denote_kind A0 -> denote_kind A0 -> denote_kind A0 with
    | Unit => fun x _ => x
    | Bit => op
    | Tuple L R =>
      fun x y => (bitwise op (fst x) (fst y), bitwise op (snd x) (snd y))
    | Vector T n => fun x y => Vector.map2 (bitwise op) x y
    end.
End Specs.

Lemma Wf_equivalence {i o} (expr : Kappa i o) :
  Wf expr -> forall var1 var2, kappa_equivalence nil (expr var1) (expr var2).
Proof. cbv [Wf]; intros; auto. Qed.
Hint Resolve Wf_equivalence : Wf.

Lemma Wf_Primitive (p : CircuitPrimitive) : Wf (fun _ => Primitive p).
Proof. cbv [Wf]; intros; apply Prim_equiv. Qed.
Hint Resolve Wf_Primitive : Wf.

(* Extra hint to force the primitive types to match *)
Hint Extern 4 (Wf (fun _ => Primitive ?p))
=> (change (@Wf (primitive_input p)
               (primitive_output p) (fun _ => Primitive p));
  eapply Wf_Primitive) : Wf.

Ltac kequiv_step :=
  lazymatch goal with
  | |- kappa_equivalence _ (Var _) (Var _) => eapply Var_equiv
  | |- kappa_equivalence _ (Abs _) (Abs _) => eapply Abs_equiv
  | |- kappa_equivalence _ (App _ _) (App _ _) => eapply App_equiv
  | |- kappa_equivalence _ (Comp _ _) (Comp _ _) => eapply Compose_equiv
  | |- @kappa_equivalence ?var1 ?var2 ?x ?y ?E (Primitive ?p) (Primitive _) =>
    change (@kappa_equivalence
              var1 var2 (primitive_input p) (primitive_output p)
              E (Primitive p) (Primitive p));
    eapply Prim_equiv
  | |- kappa_equivalence _ (Let _ _) (Let _ _) => eapply Let_equiv
  | |- kappa_equivalence _ (LetRec _ _) (LetRec _ _) => eapply Letrec_equiv
  | |- kappa_equivalence _ Id Id => eapply Id_equiv
  | |- kappa_equivalence _ (RemoveContext _) (RemoveContext _) =>
    eapply RemoveContext_equiv
  end; intros.
Ltac prove_Wf_step :=
  lazymatch goal with
  | |- kappa_equivalence _ _ _ =>
    first [ kequiv_step
          | solve [eauto with Wf] ]
  | |- List.In _ _ => cbn [List.In]; tauto
  end.
Ltac prove_Wf := cbv [Wf]; intros; repeat prove_Wf_step.

Section CombinatorWf.
  Lemma replicate_Wf A n : Wf (@Combinators.replicate n A).
  Proof. induction n; cbn [Combinators.replicate]; prove_Wf. Qed.
  Hint Resolve replicate_Wf : Wf.

  Lemma reverse_Wf A n : Wf (@Combinators.reverse n A).
  Proof. induction n; cbn [Combinators.reverse]; prove_Wf. Qed.
  Hint Resolve reverse_Wf : Wf.

  Lemma reshape_Wf A n m : Wf (@Combinators.reshape n m A).
  Proof. induction n; cbn [Combinators.reshape]; prove_Wf. Qed.
  Hint Resolve reshape_Wf : Wf.

  Lemma flatten_Wf A n m : Wf (@Combinators.flatten n m A).
  Proof. induction n; cbn [Combinators.flatten]; prove_Wf. Qed.
  Hint Resolve flatten_Wf : Wf.

  Lemma map_Wf A B n c : Wf c -> Wf (@Combinators.map n A B c).
  Proof. induction n; cbn [Combinators.map]; prove_Wf. Qed.
  Hint Resolve map_Wf : Wf.

  Lemma map2_Wf A B C n c : Wf c -> Wf (@Combinators.map2 n A B C c).
  Proof. induction n; cbn [Combinators.map2]; prove_Wf. Qed.
  Hint Resolve map2_Wf : Wf.

  Lemma foldl_Wf A B n c : Wf c -> Wf (@Combinators.foldl n A B c).
  Proof. induction n; cbv [Combinators.foldl]; prove_Wf. Qed.
  Hint Resolve foldl_Wf : Wf.

  Lemma enable_Wf A : Wf (@Combinators.enable A).
  Proof. induction A; cbn [Combinators.enable]; prove_Wf. Qed.
  Hint Resolve enable_Wf : Wf.

  Lemma bitwise_Wf A c : Wf c -> Wf (@Combinators.bitwise A c).
  Proof. induction A; cbn [Combinators.bitwise]; prove_Wf. Qed.
  Hint Resolve bitwise_Wf : Wf.

  Lemma equality_Wf A : Wf (@Combinators.equality A).
  Proof.
    induction A; cbn [Combinators.equality]; prove_Wf; [ ].
    eapply foldl_Wf; prove_Wf.
  Qed.
  Hint Resolve equality_Wf : Wf.

  Lemma mux_item_Wf A : Wf (@Combinators.mux_item A).
  Proof. cbv [Combinators.mux_item]; prove_Wf. Qed.
  Hint Resolve mux_item_Wf : Wf.
End CombinatorWf.
(* Restate hints so they last outside the section *)
Hint Resolve replicate_Wf reverse_Wf reshape_Wf flatten_Wf map_Wf map2_Wf
     foldl_Wf enable_Wf bitwise_Wf equality_Wf mux_item_Wf : Wf.

(* Miscellaneous helpful proofs for combinator equivalence *)
Section Misc.
  Lemma eqb_negb_xor x y : Bool.eqb x y = negb (xorb x y).
  Proof. destruct x, y; reflexivity. Qed.

  Lemma bitwise_or_enable A en x y :
    @bitwise A orb (enable en x) (enable (negb en) y) = if en then x else y.
  Proof.
    induction A; destruct en; cbn [bitwise enable fst snd];
      repeat match goal with
             | IH : context [bitwise _ _ _ = _] |- _ => rewrite IH
             | x : denote_kind Unit |- _ => destruct x
             | x : denote_kind Bit |- _ => destruct x
             | _ => rewrite <-surjective_pairing
             | _ => rewrite map2_map
             | _ => reflexivity
             | _ => progress autorewrite with vsimpl
             | _ => rewrite map2_ext with (g:=fun x y => x) by auto
             | _ => rewrite map2_ext with (g:=fun x y => y) by auto
             | _ => rewrite map2_drop
             | _ => rewrite map2_swap, map2_drop
             end.
  Qed.
End Misc.

(* TODO: move *)
Ltac kappa_spec_begin :=
  intros; cbn [interp_combinational'];
  repeat match goal with
         | |- context [combinational_evaluation' (CircuitArrow.Primitive ?p)] =>
           let x := constr:(combinational_evaluation' (CircuitArrow.Primitive p)) in
           let y := (eval cbv [combinational_evaluation'] in x) in
           progress change x with y
         | _ => progress cbn [denote_kind primitive_input primitive_output]
         end; fold denote_kind in *.

Create HintDb kappa_interp discriminated.
Ltac kappa_spec_step :=
  match goal with
  | H : context [interp_combinational' (_ coq_func) _ = _] |- _ => rewrite H by eauto
  | _ => progress autorewrite with kappa_interp
  | |- context [interp_combinational'] => kappa_spec_begin
  end.
Ltac kappa_spec := kappa_spec_begin; repeat kappa_spec_step.

Notation kinterp x := (interp_combinational' (x coq_func)).

(* Proofs of equivalence between circuit combinators and functional
   specifications *)
Section CombinatorEquivalence.

  Lemma replicate_correct A n (x : denote_kind A) :
    kinterp (@Combinators.replicate n A) (x, tt) = @Vector.const (denote_kind A) x n.
  Proof.
    induction n; cbn [Combinators.replicate]; kappa_spec; reflexivity.
  Qed.
  Hint Rewrite @replicate_correct : kappa_interp.

  Lemma reshape_correct {A} n m (x : Vector.t (denote_kind A) _) :
    kinterp (@Combinators.reshape n m A) (x, tt) = reshape x.
  Proof.
    induction n; intros; cbn [Combinators.reshape reshape]; kappa_spec;
      repeat destruct_pair_let; reflexivity.
  Qed.
  Hint Rewrite @reshape_correct : kappa_interp.

  Lemma map2_correct A B C n
        (c : (Tuple A << B, Unit >> ~[ KappaCat ]~> C)%CategoryLaws) :
    forall v1 v2,
      kinterp (@Combinators.map2 n A B C c) (v1, (v2, tt))
      = Vector.map2 (fun (a : denote_kind A) (b : denote_kind B) =>
                       kinterp c (a, (b, tt))) v1 v2.
  Proof.
    induction n; cbn [Combinators.map2]; intros; kappa_spec;
      autorewrite with vsimpl; rewrite ?map2_cons; reflexivity.
  Qed.
  Hint Rewrite @map2_correct : kappa_interp.

  Lemma map_correct A B n
        (c : (Tuple A Unit ~[ KappaCat ]~> B)%CategoryLaws) :
    forall v,
      kinterp (@Combinators.map n A B c) (v, tt)
      = Vector.map (fun a : denote_kind A => kinterp c (a, tt)) v.
  Proof.
    induction n; cbn [Combinators.map]; intros; kappa_spec;
      autorewrite with vsimpl; rewrite ?map_cons; reflexivity.
  Qed.
  Hint Rewrite @map_correct : kappa_interp.

  Lemma flatten_correct A n m (x : Vector.t (Vector.t (denote_kind A) _) _) :
    kinterp (@Combinators.flatten n m A) (x, tt) = flatten x.
  Proof.
    revert m x; induction n; cbn [Combinators.flatten flatten]; kappa_spec;
      repeat destruct_pair_let; reflexivity.
  Qed.
  Hint Rewrite @flatten_correct : kappa_interp.

  Lemma reverse_correct A n (x : Vector.t (denote_kind A) _):
    kinterp (@Combinators.reverse n A) (x, tt) = reverse x.
  Proof.
    induction n; cbn [Combinators.reverse reverse]; kappa_spec;
      autorewrite with vsimpl; reflexivity.
  Qed.
  Hint Rewrite @reverse_correct : kappa_interp.

  Lemma foldl_correct A B n
        (c : (Tuple B << A, Unit >> ~[ KappaCat ]~> B)%CategoryLaws) :
    forall b v,
      kinterp (Combinators.foldl (n:=n) c) (b, (v, tt))
      = Vector.fold_left (fun (b : denote_kind B) (a : denote_kind A) =>
                            kinterp c (b, (a, tt))) b v.
  Proof.
    induction n; cbn [Vector.fold_left Combinators.foldl]; kappa_spec;
      autorewrite with push_vector_fold; reflexivity.
  Qed.
  Hint Rewrite @foldl_correct : kappa_interp.

  Lemma equality_correct A (x y : denote_kind A) :
    kinterp (@Combinators.equality A) (x, (y, tt)) = denote_kind_eqb x y.
  Proof.
    induction A; cbn [Combinators.equality denote_kind_eqb];
      kappa_spec; auto using eqb_negb_xor; [ ].
    erewrite map2_ext; eauto.
  Qed.
  Hint Rewrite @equality_correct : kappa_interp.

  Lemma enable_correct A sel (x : denote_kind A) :
    kinterp (@Combinators.enable A) (sel, (x, tt)) = enable sel x.
  Proof.
    induction A; cbn [Combinators.enable enable]; kappa_spec;
      try reflexivity; [ ].
    rewrite map2_const. eauto using Vector.map_ext.
  Qed.
  Hint Rewrite @enable_correct : kappa_interp.

  Lemma bitwise_correct A
        (c : (Tuple Bit << Bit, Unit >> ~[ KappaCat ]~> Bit)%CategoryLaws) :
    forall x y : denote_kind A,
      kinterp (@Combinators.bitwise A c) (x, (y, tt))
      = bitwise (fun a b : bool => kinterp c (a, (b, tt))) x y.
  Proof.
    induction A; cbn [Combinators.bitwise bitwise]; kappa_spec;
      autorewrite with vsimpl; auto.
    eauto using map2_ext.
  Qed.
  Hint Rewrite @bitwise_correct : kappa_interp.

  Definition mux {T} (sel : bool) (x y : T) : T := if sel then x else y.
  Lemma mux_item_correct A sel (x y : denote_kind A):
    kinterp (@Combinators.mux_item A) (sel, (x, (y, tt))) = mux sel x y.
  Proof.
    cbv [Combinators.mux_item]; kappa_spec; [ ].
    rewrite bitwise_or_enable. reflexivity.
  Qed.
  Hint Rewrite @mux_item_correct : kappa_interp.
End CombinatorEquivalence.

(* needed to reduce typechecking time *)
Global Opaque Combinators.mux_item Combinators.bitwise Combinators.enable
       Combinators.equality Combinators.replicate Combinators.map2
       Combinators.map Combinators.flatten Combinators.reverse
       Combinators.reshape Combinators.foldl.

(* Restate all hints so they exist outside the section *)
Hint Rewrite @mux_item_correct @bitwise_correct @enable_correct
     @equality_correct @replicate_correct @reshape_correct @map2_correct
     @map_correct @flatten_correct @reverse_correct @reshape_correct
     @foldl_correct
  using solve [eauto] : kappa_interp.
