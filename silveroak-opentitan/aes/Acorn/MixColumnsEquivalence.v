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
Require Import Coq.micromega.Lia.
Require Import Coq.Vectors.Vector.
Require Import Coq.setoid_ring.Ring.

Require Import ExtLib.Structures.Monads.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.CombinationalPropertiesNew.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.IdentityNew.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Signal.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import AesSpec.AES256.
Require Import AesSpec.Polynomial.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.Pkg.
Require Import AcornAes.MixColumnsCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.
Existing Instance MixColumns.byteops.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma aes_transpose_correct n m (v : combType (Vec (Vec (Vec Bit 8) n) m)) :
    m <> 0 ->
    n <> 0 ->
    aes_transpose v = transpose v.
  Proof.
    intros Hm Hn.
    unfold aes_transpose.
    simpl_ident.
    rewrite map_id, map_id.
    reflexivity.
  Qed.

  Lemma poly_to_byte_to_bitvec p :
    length p = 8 -> byte_to_bitvec (MixColumns.poly_to_byte p) = of_list_sized false 8 p.
  Proof.
    intros; destruct_lists_by_length.
    repeat match goal with b : bool |- _ => destruct b end; reflexivity.
  Qed.

  Lemma bitvec_to_byte_to_poly bv :
    MixColumns.byte_to_poly (bitvec_to_byte bv) = to_list bv.
  Proof.
    constant_bitvec_cases bv; reflexivity.
  Qed.

  Lemma xorV_is_add b1 b2 :
    unIdent (xorV (n:=8) (b1, b2))
    = byte_to_bitvec (Polynomial.fadd (bitvec_to_byte b1)
                                       (bitvec_to_byte b2)).
  Proof.
    simpl_ident. fequal_list.
    cbv [Polynomial.fadd MixColumns.byteops].
    rewrite poly_to_byte_to_bitvec, !bitvec_to_byte_to_poly by length_hammer.
    cbv [Polynomial.add_poly].
    apply to_list_inj. autorewrite with push_to_list push_extend.
    rewrite to_list_of_list_sized by length_hammer.
    reflexivity.
  Qed.

  Lemma xorv_is_add b1 b2 :
    unIdent (xorv (n:=8) b1 b2)
    = byte_to_bitvec (Polynomial.fadd (bitvec_to_byte b1)
                                      (bitvec_to_byte b2)).
  Proof. apply xorV_is_add. Qed.

  (* Lemma unIdent_bind A B (x : ident A) (f : A -> ident B) : *)
  (*   unIdent (x >>= f) = unIdent (f (unIdent x)). *)
  (*   auto. *)
  (* Qed. *)

  (* Lemma unIdent_bind' A B (x : ident A) (f : A -> ident B) : *)
  (*   unIdent (x >>= f) = let y := unIdent x in unIdent (f y). *)
  (*   auto. *)
  (* Qed. *)

  Lemma aes_mul2_correct b :
    unIdent (aes_mul2 b)
    = byte_to_bitvec (Polynomial.fmul Byte.x02
                                       (bitvec_to_byte b)).
  Proof.
    cbv [combType] in *. constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  Lemma aes_mul4_correct b :
    unIdent (aes_mul4 b)
    = byte_to_bitvec (Polynomial.fmul Byte.x04
                                       (bitvec_to_byte b)).
  Proof.
    cbv [combType] in *. constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  (* (* Check signalType. *) *)
  (* Lemma indexConst_singleton (i : nat) t sz v : *)
  (*   indexConst (v : combType (Vec t sz)) i = nth_default (defaultCombValue t) i v. *)
  (*   auto. Qed. *)

  (* Lemma aes_mul2_singleton (i : nat) (v : combType (Vec Bit 8)) : *)
    (* aes_mul2 [v] = unpeel v. *)

  (* (* Print signal. *) *)
  (* (* Check @zipWith. *) *)
  (* Check CombinationalSemantics. *)
  (* Print seqType. *)
  (* (* Search zipWith. *) *)

  (* (* Lemma unIdent_zipWith (A B C : SignalType) {n : nat} *) *)
  (* (*       (x : seqType (Vec A n)) (y : seqType (Vec B n)) *) *)
  (* (*       (f : seqType A * seqType B -> cava (seqType C)) : *) *)
  (* (*   unIdent (zipWith f x y) = map2 (VectorDef.map2 (fun a b => unIdent (f _))) x y. *) *)

  (* Lemma unIdent_ret A (x : A) : unIdent (ret x) = x. *)
  (* Proof. auto. Qed. *)

  (* Hint Rewrite @unIdent_bind : ident. *)
  (* Search Traversable.mapT. *)
  (* Hint Rewrite @mapT_lident : ident. *)
  (* Hint Rewrite unIdent_ret : ident. *)
  (* Hint Rewrite indexConst_singleton : ident. *)
  (* (* Hint Rewrite xorv_unIdent : ident. *) *)
  (* (* Hint Rewrite xorV_unIdent : ident. *) *)
  (* (* Hint Rewrite @zipWith_unIdent : ident. *) *)

  (* Check map2. *)

  (* Definition HIDDEN {p : Prop} := p. *)

  (* Lemma foo x y : *)
  (*   x = byte_to_bitvec y -> bitvec_to_byte x = y. *)
  (* Proof. intros ->. apply byte_to_bitvec_to_byte. Qed. *)

  (* Ltac hide := *)
  (*   let RHS := fresh "RHS" in *)
  (*   let rest := fresh "REST" in *)
  (*   let Hhide := fresh "Hhide" in *)
  (*   match goal with *)
  (*   | [ h : HIDDEN |- _ ] => idtac *)
  (*   | [ |- unIdent (?x >>= ?f) = ?rhs ] => *)
  (*     assert (H : forall RHS rest, *)
  (*                @HIDDEN (RHS = rhs /\ rest = f) -> *)
  (*                unIdent (x >>= rest) = RHS); *)
  (*     [intros ? ? Hhide | refine (H rhs f _); split; reflexivity ] *)
  (*   end. *)

  (* Ltac rehide := *)
  (*   let H0 := fresh "H" in *)
  (*   let H1 := fresh "H" in *)
  (*   let y := fresh "x" in *)
  (*   let Hy := fresh "Heqx" in *)
  (*     lazymatch goal with *)
  (*     | [ H : @HIDDEN (?RHS = ?rhs /\ ?rest = ?f) |- unIdent (?rest ?x) = ?RHS ] => *)
  (*       destruct H as [H0 H1]; *)
  (*       remember x as y eqn:Hy; *)
  (*       subst rest; *)
  (*       match goal with *)
  (*       | [ h : HIDDEN |- _ ] => idtac *)
  (*       | [ |- unIdent (?x >>= ?f) = ?rhs ] => *)
  (*         assert (H : forall rest, *)
  (*                    @HIDDEN (RHS = rhs /\ rest = f) -> *)
  (*                    unIdent (x >>= rest) = RHS); *)
  (*         [intros ? H; clear H0; rehide | refine (H f _); split; auto ] *)
  (*       end *)
  (*     | [ H : @HIDDEN (?RHS = ?rhs /\ ?rest = ?f) |- _ ] => *)
  (*       destruct H as [H0 ->]; *)
  (*       (repeat rewrite (@MonadLaws.bind_associativity _ _ MonadFacts.MonadLaws_ident)); *)
  (*       match goal with *)
  (*         | |- unIdent (?x >>= ?f') = ?RHS => *)
  (*           assert (H : forall rest, *)
  (*                      @HIDDEN (RHS = rhs /\ rest = f') -> *)
  (*                      unIdent (x >>= rest) = RHS); *)
  (*           [intros ? H; clear H0 | refine (H f' _); split; auto ] *)
  (*       end *)
  (*     | _ => idtac *)
  (*     end. *)

  (* Ltac subst_x heqx := *)
  (*   let Heq' := fresh "Heqx'" in *)
  (*   lazymatch goal with *)
  (*   | heqx : ?x = [?y] |- _ => *)
  (*     let v := fresh "v" in *)
  (*     remember y as v eqn:Heq'; subst x; *)
  (*     try apply foo in Heq' *)
  (*   | heqx : ?x = ?y |- _ => *)
  (*     subst x *)
  (*   end. *)

  (* Ltac bind_step Heqx := *)
  (*   try (subst_x Heqx); hide; autorewrite with ident; *)
  (*   rehide. *)

  (* Ltac destruct_vector v := *)
  (*   match type of v with *)
  (*   | t _ (S ?n) => *)
  (*     let a := fresh "a" in *)
  (*     let n := fresh "n" in *)
  (*     let v' := fresh "v" in *)
  (*     dependent inversion v as [| a n v']; *)
  (*     subst n; *)
  (*     try clear v; *)
  (*   (* rename v' into v; *) *)
  (*     idtac *)
  (*   | t _ 0 => inversion v *)
  (*   end. *)

  (* Ltac foo Heqx := *)
  (*       replace (nil (seqType (Vec Bit 8) * seqType (Vec Bit 8))) with (map (fun x : t bool 8 * t bool 8 => ([fst x], [snd x])) (nil _)) in Heqx; [| reflexivity]; *)
  (*   repeat lazymatch goal with *)
  (*   | Heqx : context H [ cons ?A ([?x], [?y])%list ?n (map ?f ?xs) ] |- _ => *)
  (*     change (cons (seqType (Vec Bit 8) * seqType (Vec Bit 8)) ([x], [y])%list n (map f xs)) *)
  (*       with (map (fun a : byte * byte => f a) (cons (t bool 8 * t bool 8) (x, y) n xs)) in Heqx *)
  (*   end. *)

  (* Search unpeel. *)
  (* Lemma unpeel_singleton {A B n} (f : A -> combType B) (v : Vector.t A n) : *)

  (* Check unpeel_singleton. *)

  (* Lemma unpeel_nil {A} : *)
  (*   unpeel (nil (seqType A)) = []. *)
  (* Proof. reflexivity. Qed. *)

  (* Definition List_map {A B n} : forall (f : t A n -> B) (v : list (t A n)), list B := *)
  (*   match n with *)
  (*   | 0 => fun f v => [f (nil _)] *)
  (*   | S n => fun f v => List.map f v *)
  (*   end. *)

  (* Definition isSingleton {A} (xs : list A) : option A := *)
  (*   match xs with *)
  (*   | [] => None *)
  (*   | [x] => Some x *)
  (*   | _ :: _ => None *)
  (*   end. *)

  (* Search @Traversable. *)
  (* Check @Traversable.mapT. *)
  (* Search Applicative.Applicative. *)

  (* Require Import Coq.Program.Equality. *)

  (* Lemma unpeel_cons {A n} (v : Vector.t (seqType A) n) *)
  (*       (v' : Vector.t (combType A) n) *)
  (*       (x : combType A) : *)
  (*   n <> 0 -> *)
  (*   Some v' = Traversable.mapT isSingleton v -> *)
  (*   unpeel v = [v']. *)
  (* Proof. *)
  (*   intros H'' H. *)
  (*   assert (H' : v = map (fun a => [a]%list) v'). *)
  (*   { clear H''. revert v H. induction v'; intros v H. *)
  (*     - dependent induction v. auto. *)
  (*     - dependent induction v. *)
  (*       clear IHv. simpl. *)
  (*       simpl in H. destruct h0; simpl in H; [inversion H|]. *)
  (*       destruct h0; [| inversion H]. *)
  (*       pose (f (x : option (Vector.t (combType A) (S n))) := *)
  (*               match x return (Vector.t (combType A) (n)) with *)
  (*               | None => v' *)
  (*               | Some v => tl v *)
  (*               end ). *)
  (*       pose (g (x : option (Vector.t (combType A) (S n))) := *)
  (*               match x return (combType A) with *)
  (*               | None => h *)
  (*               | Some v => hd v *)
  (*               end ). *)
  (*       assert (HH := f_equal f H). *)
  (*       assert (HH' := f_equal g H). *)
  (*       remember (mapT_vector isSingleton v) as k; destruct k; *)
  (*         simpl in HH, HH'; [| inversion H]. *)
  (*       subst. *)
  (*       rewrite <- (IHv' v); auto. *)
  (*   } *)
  (*   rewrite H', unpeel_singleton, map_id; auto. *)
  (* Qed. *)

  (* Instance MonadLaws_option : @MonadLaws option _. *)
  (* Proof. *)
  (*   constructor. *)
  (*   - intros. reflexivity. *)
  (*   - intros. destruct aM; auto. *)
  (* Qed. *)

  Hint Rewrite xorv_is_add using solve [eauto] : simpl_ident.
  Hint Rewrite xorV_is_add using solve [eauto] : simpl_ident.
  Hint Rewrite aes_mul2_correct using solve [eauto] : simpl_ident.
  Hint Rewrite aes_mul4_correct using solve [eauto] : simpl_ident.

  Add Ring bytering : MixColumns.ByteTheory.
  Local Open Scope poly_scope.

  Ltac prering :=
    change Byte.x03 with (Byte.x02 + Byte.x01);
    change Byte.x04 with (Byte.x02 * Byte.x02);
    change Byte.x05 with (Byte.x02 * Byte.x02 + Byte.x01);
    change Byte.x06 with (Byte.x02 * (Byte.x02 + Byte.x01));
    change Byte.x07 with (Byte.x02 * (Byte.x02 + Byte.x01) + Byte.x01);
    change Byte.x08 with (Byte.x02 * (Byte.x02 * Byte.x02));
    change Byte.x09 with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x01);
    change Byte.x0a with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02);
    change Byte.x0b with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 + Byte.x01);
    change Byte.x0c with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * Byte.x02);
    change Byte.x0d with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * Byte.x02 + Byte.x01);
    change Byte.x0e with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * (Byte.x02 + Byte.x01));
    change Byte.x0e with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * (Byte.x02 + Byte.x01) + Byte.x01);
    change Byte.x01 with fone;
    change (bitvec_to_byte zero_byte) with fzero.


  Lemma mix_single_column_equiv (is_decrypt : bool) (col : Vector.t byte 4) :
    unIdent (aes_mix_single_column is_decrypt col)
    = if is_decrypt
       then map byte_to_bitvec
                (MixColumns.inv_mix_single_column (map bitvec_to_byte col))
       else map byte_to_bitvec
                (MixColumns.mix_single_column (map bitvec_to_byte col)).
  Proof.
    constant_vector_simpl col.
    unfold MixColumns.inv_mix_single_column, MixColumns.mix_single_column.
    autorewrite with push_vector_map vsimpl push_vector_fold.

    unfold aes_mix_single_column.
    simpl_ident.
    cbv [localSignal CombinationalSemantics].
    simpl_ident.
    destruct is_decrypt.
    all: fequal_vector.
    all: cbn [nth_default map]; simpl_ident.
    all: repeat rewrite byte_to_bitvec_to_byte.
    all: f_equal.
    all: ring_simplify; prering.
    all: repeat match goal with
         | |- context [ bitvec_to_byte ?x ] =>
           let y := fresh "x" in
           generalize (bitvec_to_byte x); intro y
         | x := _ |- _ => clear x
         | x : _ |- _ => clear x
                end.
    all: ring.
  Qed.

  Lemma mix_columns_equiv (is_decrypt : bool) (st : state) :
    combinational (aes_mix_columns [is_decrypt] [st])
    = [AES256.aes_mix_columns_circuit_spec is_decrypt st].
  Proof.
    cbv [aes_mix_columns combinational]. simpl_ident.
    rewrite aes_transpose_correct by lia.
    rewrite (peel_singleton (A:=Vec (Vec Bit 8) 4)).
    rewrite map_map.
    erewrite map_ext by apply mix_single_column_equiv.
    rewrite (unpeel_singleton (B:=Vec (Vec Bit 8) 4)) by congruence.
    rewrite aes_transpose_correct by lia.
    cbv [AES256.aes_mix_columns_circuit_spec
           AES256.mix_columns AES256.inv_mix_columns
           MixColumns.mix_columns MixColumns.inv_mix_columns].
    cbv [from_flat to_flat BigEndian.to_rows BigEndian.from_rows].
    autorewrite with conversions.
    (* consolidate all the repeated maps *)
    rewrite !transpose_map_map, !map_map.
    rewrite <-!transpose_map_map, !map_map.
    destruct is_decrypt;
      repeat lazymatch goal with
             | |- [_] = [_] => apply f_equal
             | |- transpose _ = transpose _ => apply f_equal
             | |- map _ ?v = map _ ?v => apply map_ext; intros
             | _ => reflexivity
             end.
  Qed.
End Equivalence.
