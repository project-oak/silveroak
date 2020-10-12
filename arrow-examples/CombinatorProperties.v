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

From Arrow Require Import Category Arrow.
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

  Lemma rewrite_or_default_refl A :
    circuit_equiv _ _ (rewrite_or_default A A) (fun x => x).
  Proof.
    induction A; cbn [rewrite_or_default] in *; arrowsimpl;
      circuit_spec; autorewrite with vsimpl;
        try apply surjective_pairing; eauto.
  Qed.
End Misc.
Hint Resolve rewrite_or_default_refl : circuit_spec_correctness.

(* Proofs of equivalence between circuit combinators and functional
   specifications *)
Section CombinatorEquivalence.
  Lemma replicate_correct A n :
    obeys_spec (@Combinators.replicate n A)
               (fun x : denote_kind A * unit => Vector.const (fst x) n).
  Proof.
    induction n; cbn [Combinators.replicate]; circuit_spec; reflexivity.
  Qed.
  Hint Resolve replicate_correct : circuit_spec_correctness.

  Lemma reshape_correct {A} n m :
    obeys_spec (@Combinators.reshape n m A)
               (fun x : Vector.t (denote_kind A) _ * unit =>
                  @reshape (denote_kind A) _ _ (fst x)).
  Proof.
    induction n; intros; cbn [Combinators.reshape reshape].
    { circuit_spec. reflexivity. }
    { circuit_spec; [ ].  autorewrite with vsimpl.
      repeat destruct_pair_let. reflexivity. }
  Qed.
  Hint Resolve reshape_correct : circuit_spec_correctness.

  Lemma map2_correct A B C n c (f : denote_kind A -> denote_kind B -> denote_kind C) :
    @obeys_spec (Tuple A (Tuple B Unit)) C c
                (fun abu : denote_kind A * (denote_kind B * unit) =>
                   f (fst abu) (fst (snd abu))) ->
    obeys_spec (@Combinators.map2 n A B C c)
               (fun v1v2u : Vector.t (denote_kind A) n
                          * (Vector.t (denote_kind B) n * unit) =>
                  Vector.map2 f (fst v1v2u) (fst (snd v1v2u))).
  Proof.
    induction n; cbn [Combinators.map2]; intros; circuit_spec;
      autorewrite with vsimpl; rewrite ?map2_cons; reflexivity.
  Qed.
  Hint Resolve map2_correct : circuit_spec_correctness.
  Hint Extern 2 (obeys_spec (Combinators.map2 _) _)
  => (eapply map2_correct; circuit_spec_crush) : circuit_spec_correctness.

  Lemma map_correct A B n c (f : denote_kind A -> denote_kind B) :
    @obeys_spec (Tuple A Unit) B c (fun x : denote_kind A * unit => f (fst x)) ->
    obeys_spec (@Combinators.map n A B c)
               (fun x : Vector.t (denote_kind A) _ * unit => Vector.map f (fst x)).
  Proof.
    induction n; cbn [Combinators.map]; intros; circuit_spec;
      autorewrite with vsimpl; rewrite ?map_cons; reflexivity.
  Qed.
  Hint Resolve map_correct : circuit_spec_correctness.
  Hint Extern 2 (obeys_spec (Combinators.map _) _)
  => (eapply map_correct; circuit_spec_crush) : circuit_spec_correctness.

  Lemma flatten_correct A n m :
    obeys_spec (@Combinators.flatten n m A)
               (fun x : Vector.t (Vector.t (denote_kind A) _) _ * unit =>
                  @flatten (denote_kind _) _ _ (fst x)).
  Proof.
    revert m; induction n; cbn [Combinators.flatten flatten]; intros.
    { circuit_spec; reflexivity. }
    { circuit_spec; [ ]. destruct_pair_let.
      autorewrite with vsimpl. reflexivity. }
  Qed.
  Hint Resolve flatten_correct : circuit_spec_correctness.

  Lemma reverse_correct A n :
    obeys_spec (@Combinators.reverse n A)
               (fun x : Vector.t (denote_kind A) _ * unit  =>
                  @reverse (denote_kind A) _ (fst x)).
  Proof.
    induction n; cbn [Combinators.reverse reverse]; circuit_spec;
      autorewrite with vsimpl; reflexivity.
  Qed.
  Hint Resolve reverse_correct : circuit_spec_correctness.

  Lemma foldl_correct A B n c (f : denote_kind B -> denote_kind A -> denote_kind B) :
    @obeys_spec (Tuple B (Tuple A Unit)) _ c
                (fun x : denote_kind B * (denote_kind A * unit) => f (fst x) (fst (snd x))) ->
    obeys_spec (Combinators.foldl (n:=n) c)
               (fun x : denote_kind B * (Vector.t (denote_kind A) _ * unit) =>
                  Vector.fold_left f (fst x) (fst (snd x))).
  Proof.
    intros; induction n; cbn [Vector.fold_left Combinators.foldl]; circuit_spec.
    { eapply Vector.case0 with (v:=fst (snd (fst _))). reflexivity. }
    { autorewrite with push_vector_fold vsimpl. reflexivity. }
  Qed.
  Hint Resolve foldl_correct : circuit_spec_correctness.
  Hint Extern 2 (obeys_spec (Combinators.foldl _) _)
  => (eapply foldl_correct; circuit_spec_crush) : circuit_spec_correctness.

  Lemma equality_correct A :
    obeys_spec (@Combinators.equality A)
               (fun x : denote_kind A * (denote_kind A * unit) =>
                  denote_kind_eqb (fst x) (fst (snd x))).
  Proof.
    induction A; cbn [Combinators.equality denote_kind_eqb];
      circuit_spec; auto using eqb_negb_xor.
  Qed.
  Hint Resolve equality_correct : circuit_spec_correctness.

  Lemma enable_correct A :
    obeys_spec (@Combinators.enable A)
               (fun x : bool * (denote_kind A * unit) => enable (fst x) (fst (snd x))).
  Proof.
    induction A; cbn [Combinators.enable enable]; circuit_spec;
      try reflexivity; [ ].
    rewrite map2_const. autorewrite with vsimpl. reflexivity.
  Qed.
  Hint Resolve enable_correct : circuit_spec_correctness.

  Lemma bitwise_correct A c op :
    @obeys_spec (Tuple Bit (Tuple Bit Unit)) _ c
                (fun x : bool * (bool * unit) => op (fst x) (fst (snd x))) ->
    obeys_spec (@Combinators.bitwise A c)
               (fun x : denote_kind A * (denote_kind A * unit) =>
                  bitwise op (fst x) (fst (snd x))).
  Proof.
    intros.
    induction A; cbn [Combinators.bitwise bitwise]; circuit_spec;
      autorewrite with vsimpl; auto.
  Qed.
  Hint Resolve bitwise_correct : circuit_spec_correctness.
  Hint Extern 2 (obeys_spec (Combinators.bitwise _) _)
  => (eapply bitwise_correct; circuit_spec_crush) : circuit_spec_correctness.

  Lemma mux_item_correct A :
    obeys_spec (@Combinators.mux_item A)
               (fun x : bool * (denote_kind A * (denote_kind A * unit)) =>
                  if (fst x) then (fst (snd x)) else (fst (snd (snd x)))).
  Proof.
    cbv [Combinators.mux_item]; circuit_spec; [ ].
    rewrite bitwise_or_enable. reflexivity.
  Qed.
  Hint Resolve mux_item_correct : circuit_spec_correctness.
End CombinatorEquivalence.

(* Restate all hints so they exist outside the section *)
Hint Resolve mux_item_correct bitwise_correct enable_correct
     equality_correct replicate_correct reshape_correct map2_correct
     map_correct flatten_correct reverse_correct foldl_correct
  : circuit_spec_correctness.

(* Because the some lemmas produce an [obeys_spec] subgoal, we tell [eauto] it
   can also try to solve their subgoals using [circuit_spec_crush] *)
Hint Extern 2 (obeys_spec (Combinators.map _) _)
=> (eapply map_correct; circuit_spec_crush) : circuit_spec_correctness.
Hint Extern 2 (obeys_spec (Combinators.map2 _) _)
=> (eapply map2_correct; circuit_spec_crush) : circuit_spec_correctness.
  Hint Extern 2 (obeys_spec (Combinators.foldl _) _)
  => (eapply foldl_correct; circuit_spec_crush) : circuit_spec_correctness.
Hint Extern 2 (obeys_spec (Combinators.bitwise _) _)
=> (eapply bitwise_correct; circuit_spec_crush) : circuit_spec_correctness.
