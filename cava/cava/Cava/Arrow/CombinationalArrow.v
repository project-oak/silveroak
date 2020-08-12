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

From Coq Require Import Bool ZArith NArith NaryFunctions Vector Lia.
From Arrow Require Import Category Arrow.
From Cava.Arrow Require Import CavaArrow PropArrow.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.

(******************************************************************************)
(* Evaluation as function evaluation, no delay elements or loops              *)
(******************************************************************************)

Section instance.

Instance CoqKindMaybeCategory : Category Kind := {
  morphism X Y := denote_kind X -> denote_kind Y;
  compose _ _ _ f g x := f (g x);
  id X x := x;
}.

Instance CoqKindMaybeArrow : Arrow _ CoqKindMaybeCategory Unit Tuple := {
  first _ _ _ f i := (f (fst i), snd i);
  second _ _ _ f i := (fst i, f (snd i));

  cancelr X x := (fst x);
  cancell X x := (snd x);

  uncancell _ x := (tt, x);
  uncancelr _ x := (x, tt);

  assoc _ _ _ i := (fst (fst i), (snd (fst i), snd i));
  unassoc _ _ _ i := ((fst i, fst (snd i)), snd (snd i));
}.

Instance CombinationalDrop : ArrowDrop CoqKindMaybeArrow := { drop _ x := tt }.
Instance CombinationalCopy : ArrowCopy CoqKindMaybeArrow := { copy _ x := (pair x x) }.
Instance CombinationalSwap : ArrowSwap CoqKindMaybeArrow := { swap _ _ x := (snd x, fst x) }.
Instance CombinationalLoop : ArrowLoop CoqKindMaybeArrow := 
  { loopl _ _ _ _ _ := kind_default _; loopr _ _ _ _ _ := kind_default _; }.
Instance CombinationalSTKC : ArrowSTKC CoqKindMaybeArrow := { }.

Definition vec_head {n o} (v: t o (S n)): o := 
  match v with
  | x::_ => x
  end.
Definition vec_tail {n o} (v: t o (S n)): t o n := 
  match v with
  | _::x => x
  end.

#[refine] Instance Combinational : Cava := {
  cava_arrow := CoqKindMaybeArrow;
  constant b _ := b;
  constant_bitvec n v _ := (N2Bv_sized n v);

  mk_module _ _ _name f := f;

  not_gate b := (negb (fst b));
  and_gate '(x, y) := (andb x (fst y));
  nand_gate '(x, y) := (negb (andb x (fst y)));
  or_gate '(x, y) := (orb x (fst y));
  nor_gate '(x, y) := (negb (orb x (fst y)));
  xor_gate '(x, y) := (xorb x (fst y));
  xnor_gate '(x, y) := (negb (xorb x (fst y)));
  buf_gate x := (fst x);
  delay_gate _ _ := kind_default _;

  xorcy '(x, y) := (xorb x (fst y));
  muxcy i := (if fst i then fst (fst (snd i)) else snd (fst (snd i)));

  unsigned_add m n s '(av, (bv, _)) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c);

  unsigned_sub s '(av, (bv, _)) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a - b)%N in (*todo: This is likely incorrect on underflow *)
    (Ndigits.N2Bv_sized s c);

  lut n f '(i,_) :=
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ i));

  empty_vec o _ := (Vector.nil (denote_kind o));
  index n o x := 
    match Arith.Compare_dec.lt_dec (bitvec_to_nat (fst (snd x))) n with
    | left Hlt => (nth_order (fst x) Hlt)
    | right Hnlt => kind_default _
    end;

  cons n o '(x, (v,_)) := (x :: v);
  snoc n o '(v, (x,_)) := 
    let v' := (v ++ [x]) 
    in match Nat.eq_dec (n + 1) (S n)  with 
      | left Heq => rew [fun x => (denote_kind (Vector o x))] Heq in v'
      | right Hneq => (ltac:(exfalso;lia))
      end;
  uncons n o v := (vec_head (fst v), vec_tail (fst v));
  unsnoc n o v :=
    let v' := match Arith.Compare_dec.le_dec n (S n)  with 
      | left Hlt => take n Hlt (fst v)
      | right Hnlt => (ltac:(exfalso; abstract lia))
      end in
    (v', last (fst v));
  concat n m o '(x, (y, _)) := (Vector.append x y);

  split n m o x :=
    (Vector.splitat n (fst x));

  slice n x y o H1 H2 v := 
    match Nat.eq_dec n (y + (n - y)) with 
      | left Heq =>
        let '(_, v) := splitat y (rew [fun x => Vector.t (denote_kind o) x] Heq in (fst v))
        in 
          match Nat.eq_dec (n-y) ((x - y + 1) + (n - x - 1)) with 
          | left Heq => _
          | right Hneq => (ltac:(exfalso; abstract lia))
          end
      | right Hneq => (ltac:(exfalso; abstract lia))
      end;
}.
Proof.
  (* slice *)
  - cbn.
    intros.
    rewrite Heq in v.
    apply (splitat (x-y+1)) in v.
    exact (fst v).
Defined.

End instance.

Local Open Scope category_scope.

Definition combinational_evaluation {x y: Kind}
  (circuit: forall cava: Cava, x ~> y)
  (ok: is_combinational circuit)
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y :=
  (insert_rightmost_tt1 x >>> circuit Combinational) i.