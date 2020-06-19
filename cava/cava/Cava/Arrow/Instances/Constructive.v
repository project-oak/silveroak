From Coq Require Import Bool List NaryFunctions NArith Omega.
Import ListNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

Set Implicit Arguments.

Inductive structure: Kind -> Kind -> Type :=
  | Id:          forall {x}, structure x x
  | Compose:     forall {x y z}, structure y z -> structure x y -> structure x z
  | Copy:        forall {x}, structure x <<x, x>>
  | Drop:        forall {x}, structure x Unit
  | Swap:        forall {x y}, structure <<x, y>> <<y, x>>

  | First:       forall {x y z}, structure x y -> structure <<x, z>> <<y, z>>
  | Second:      forall {x y z}, structure x y -> structure <<z, x>> <<z, y>>

  | Cancelr:     forall {x}, structure <<x, Unit>> x
  | Cancell:     forall {x}, structure <<Unit, x>> x

  | Uncancell:   forall {x}, structure x <<Unit, x>>
  | Uncancelr:   forall {x}, structure x <<x, Unit>>

  | Assoc:       forall {x y z}, structure << <<x, y>>, z >> << x, <<y, z>> >>
  | Unassoc:     forall {x y z}, structure << x, <<y, z>> >> << <<x, y>>, z >>

  | LoopL:      forall {x y z}, structure <<z, x>> <<z, y>> -> structure x y
  | LoopR:      forall {x y z}, structure <<x, z>> <<y, z>> -> structure x y

  | Constant:    bool -> structure Unit Bit
  | ConstantBitVec: forall {n}, N -> structure Unit (Vector n Bit)

  | NotGate:     structure Bit Bit
  | AndGate:     structure << Bit, Bit >> Bit
  | NandGate:    structure << Bit, Bit >> Bit
  | OrGate:      structure << Bit, Bit >> Bit
  | NorGate:     structure << Bit, Bit >> Bit
  | XorGate:     structure << Bit, Bit >> Bit
  | XnorGate:    structure << Bit, Bit >> Bit
  | BufGate:     structure Bit Bit
  | DelayGate:   forall {o}, structure o o

  | Xorcy:       structure << Bit, Bit >> Bit
  | Muxcy:       structure << Bit, << Bit, Bit >> >> Bit

  | UnsignedAdd: forall a b s, structure << Vector a Bit, Vector b Bit >> (Vector s Bit)

  | Lut: forall n (f: bool^^n --> bool), structure (Vector n Bit) Bit

  | IndexVec: forall {n o}, structure << Vector n o, Vector (log2_up_min_1 n) Bit >> o
  | SliceVec: forall {n} x y {o}, x < n -> y <= x -> structure << Vector n o >> (Vector (x - y + 1) o)
  | ToVec: forall {o}, structure o (Vector 1 o)
  | Append: forall {n o}, structure << Vector n o, o >> (Vector (n+1) o)
  | Concat: forall {n m o}, structure << Vector n o, Vector m o >> (Vector (n+m) o)
  | Split: forall {n m o}, m < n -> structure << Vector n o >> <<Vector m o , Vector (n-m) o>>.

Inductive st_equiv : forall (i o: Kind), structure i o -> structure i o -> Prop :=
  | st_refl:    forall x y f, @st_equiv x y f f
  | st_sym:     forall x y f g, st_equiv g f -> @st_equiv x y f g
  | st_trans:   forall x y f g h, st_equiv f g -> st_equiv g h -> @st_equiv x y f h
  | st_compose: forall x y z f g h i, @st_equiv x y f g -> @st_equiv y z h i -> st_equiv (Compose h f) (Compose i g)
  | st_id_left: forall x y f, @st_equiv x y (Compose f Id) f
  | st_id_right:forall x y f, @st_equiv x y (Compose Id f) f
  | st_assoc:   forall x y z w
                      (f: structure x y) (g: structure y z) (h: structure z w),
                      @st_equiv x w (Compose h (Compose g f)) (Compose (Compose h g) f)

  (* ad-hoc equivalences *)
  | st_first_cancelr: forall x y f,
    st_equiv (Compose Cancelr (@First x y Unit f)) (Compose f Cancelr)
  | st_second_cancell: forall x y f,
    st_equiv (Compose Cancell (@Second x y Unit f)) (Compose f Cancell)

  | st_uncancelr_first:
    forall x y f, st_equiv (Compose (@First x y Unit f) Uncancelr) (Compose Uncancelr f)
  | st_uncancell_second: forall x y f, st_equiv (Compose (@Second x y Unit f) Uncancell) (Compose Uncancell f)

  | st_assoc_iso: forall x y z w s t (f: structure x y) (g: structure z w) (h: structure s t),
    st_equiv
    (Compose (Compose (Second (Compose (Second h) (First g))) (First f)) Assoc)
    (Compose Assoc (Compose (Second h) (First (Compose (Second g) (First f))) ))

  | st_unassoc_iso: forall x y z w s t (f: structure x y) (g: structure z w) (h: structure s t),
    st_equiv
    (Compose (Compose (Second h) (First (Compose (Second g) (First f)))) Unassoc)
    (Compose Unassoc (Compose (Second (Compose (Second h) (First g))) (First f) ))

  (* ad-hoc equivalences *)
  | st_cancelr_unit_uncancelr: forall x, st_equiv (Compose (@Uncancelr x) (@Cancelr x)) Id
  | st_cancell_unit_uncancell: forall x, st_equiv (Compose (@Uncancell x) (@Cancell x)) Id

  | st_uncancelr_cancelr: forall x, st_equiv (Compose (@Cancelr x) (@Uncancelr x)) Id
  | st_uncancell_cancell: forall x, st_equiv (Compose (@Cancell x) (@Uncancell x)) Id

  | st_drop_annhilates: forall x y (f: structure x y), st_equiv (Compose Drop f) Drop

  | st_cancelr_unit_is_drop: st_equiv (@Cancelr Unit) Drop
  | st_cancell_unit_is_drop: st_equiv (@Cancell Unit) Drop

  | st_first_first: forall x y z w (f: structure x y) (g: structure y z),
    st_equiv (Compose (@First _ _ w g) (First f)) (First (Compose g f))
  | st_second_second: forall x y z w (f: structure x y) (g: structure y z),
    st_equiv (Compose (@Second _ _ w g) (Second f)) (Second (Compose g f))

  | st_swap_swap: forall x y, st_equiv (Compose Swap (@Swap x y)) Id

  | st_first_id: forall x w, st_equiv (@First x x w Id) Id
  | st_second_id: forall x w, st_equiv (@Second x x w Id) Id

  | st_first_f: forall x y w (f: structure x y) (g: structure x y),
    st_equiv f g -> st_equiv (@First _ _ w f) (First g)
  | st_second_f: forall x y w (f: structure x y) (g: structure x y),
    st_equiv f g -> st_equiv (@Second _ _ w f) (Second g)

  | st_assoc_unassoc: forall x y z, st_equiv (Compose (@Unassoc x y z) (@Assoc x y z)) Id
  | st_unassoc_assoc: forall x y z, st_equiv (Compose (@Assoc x y z) (@Unassoc x y z)) Id.

(*TODO: *)
Fixpoint structural_simplification {i o} (s: structure i o): structure i o := s.

Hint Immediate st_refl : core.
Hint Immediate st_sym : core.
Hint Immediate st_trans : core.

Fixpoint toCava {i o} (expr: structure i o) (cava: Cava) 
  : i ~> o :=
  match expr with
  | Id           => id
  | Compose g f  => compose (toCava g cava) (toCava f cava)
  | Copy         => copy
  | Drop         => drop
  | Swap         => swap

  | First f    => first (toCava f cava)
  | Second f   => second (toCava f cava)

  | Cancelr    => cancelr
  | Cancell    => cancell

  | Uncancell  => uncancell
  | Uncancelr  => uncancelr

  | Assoc   => assoc
  | Unassoc => unassoc

  | LoopL c => loopl (toCava c cava)
  | LoopR c => loopr (toCava c cava)

  | Constant b        => constant b
  | @ConstantBitVec n v => constant_bitvec n v

  | NotGate   => not_gate
  | AndGate   => and_gate
  | NandGate  => nand_gate
  | OrGate    => or_gate
  | NorGate   => nor_gate
  | XorGate   => xor_gate
  | XnorGate  => xnor_gate
  | BufGate   => buf_gate
  | DelayGate => delay_gate

  | Xorcy     => xorcy
  | Muxcy     => muxcy

  | UnsignedAdd a b s => unsigned_add a b s

  | Lut n f => lut n f
  | IndexVec => index_vec _ _
  | SliceVec H1 H2 => slice_vec _ _ _ _ H1 H2
  | ToVec => to_vec _
  | Append => append _ _
  | Concat => concat _ _ _
  | Split H => split _ _ _ H
  end.

Lemma toCavaIterative: forall i o x (Cava: Cava) (e1: structure i x) (e2: structure x o),
  toCava (Compose e2 e1) Cava = toCava e1 Cava >>> toCava e2 Cava.
Proof.
  auto.
Qed.

#[refine] Instance StructureCategory : Category Kind := {
  morphism X Y := structure X Y;
  compose X Y Z f g := Compose f g;
  id X := Id;

  morphism_equivalence x y f g := st_equiv f g;
}.
Proof.
  intros.
  apply RelationClasses.Build_Equivalence.
  unfold RelationClasses.Reflexive. auto.
  unfold RelationClasses.Symmetric. auto.
  unfold RelationClasses.Transitive. intros. apply (st_trans H H0).

  intros.
  unfold Morphisms.Proper.
  refine (fun f => _). intros.
  refine (fun g => _). intros.
  apply (st_compose H0 H).

  intros. exact (st_id_left f).
  intros. exact (st_id_right f).
  intros. exact (st_assoc f g h).
Defined.

Instance StructureArrow : Arrow Kind StructureCategory Unit Tuple := {
  first _ _ _ f := First f;
  second _ _ _ f := Second f;
  cancelr X := @Cancelr X;
  cancell X := @Cancell X;

  uncancell X := @Uncancell X;
  uncancelr X := @Uncancelr X;

  assoc X Y Z := @Assoc X Y Z;
  unassoc X Y Z := @Unassoc X Y Z;

  first_cancelr := st_first_cancelr;
  second_cancell := st_second_cancell;

  uncancelr_first := st_uncancelr_first;
  uncancell_second := st_uncancell_second;

  assoc_iso := st_assoc_iso;
  unassoc_iso := st_unassoc_iso;
}.

Instance ConstructiveDrop : ArrowDrop StructureArrow := { drop := @Drop }.
Instance ConstructiveSwap : ArrowSwap StructureArrow := { swap := @Swap }.
Instance ConstructiveCopy : ArrowCopy StructureArrow := { copy := @Copy }.
Instance ConstructiveLoop : ArrowLoop StructureArrow := {
  loopl _ _ _ c := LoopL c;
  loopr _ _ _ c := LoopR c;
}.

(* Instance ConstructiveCircuitLaws : CircuitLaws ConstructiveArr _ _ _ := {
  cancelr_unit_uncancelr := st_cancelr_unit_uncancelr;
  cancell_unit_uncancell := st_cancell_unit_uncancell;

  uncancelr_cancelr := st_uncancelr_cancelr;
  uncancell_cancell := st_uncancell_cancell;

  drop_annhilates := st_drop_annhilates;

  cancelr_unit_is_drop := st_cancelr_unit_is_drop;
  cancell_unit_is_drop := st_cancell_unit_is_drop;

  first_first := st_first_first;
  second_second := st_second_second;

  swap_swap := st_swap_swap;

  first_id := st_first_id;
  second_id := st_second_id;

  first_f := st_first_f;
  second_f := st_second_f;
}. *)

Instance StructureCava : Cava := {
  constant := Constant;
  constant_bitvec n := ConstantBitVec;

  not_gate := NotGate;
  and_gate := AndGate;
  nand_gate := NandGate;
  or_gate := OrGate;
  nor_gate := NorGate;
  xor_gate := XorGate;
  xnor_gate := XnorGate;
  buf_gate := BufGate;
  delay_gate o := DelayGate;

  xorcy := Xorcy;
  muxcy := Muxcy;

  unsigned_add := UnsignedAdd;

  lut n f := Lut n f;
  index_vec n o := IndexVec;
  slice_vec n := SliceVec ;
  to_vec o := ToVec;
  append n o := Append;
  concat n m o := Concat;
  split n m o := Split;
}.

Close Scope N_scope.

Fixpoint insert_rightmost_unit (ty: Kind): Kind :=
match ty with
| Tuple l r => Tuple l (insert_rightmost_unit r)
| Unit => Unit
| x => Tuple x Unit
end.

Fixpoint remove_rightmost_unit (ty: Kind): Kind :=
match ty with
| Tuple l Unit => l
| Tuple l r => Tuple l (remove_rightmost_unit r)
| x => x
end.

Fixpoint arg_length (ty: Kind) :=
match ty with
| Tuple _ r => 1 + (arg_length r)
| _ => 0
end.

Definition arg_length_order (ty1 ty2: Kind) :=
  arg_length ty1 < arg_length ty2.

Lemma arg_length_order_wf': forall len ty, arg_length ty < len -> Acc arg_length_order ty.
Proof.
  unfold arg_length_order; induction len; intros.
  - inversion H.
  - refine (Acc_intro _ _); intros.
    eapply (IHlen y).
    omega.
Defined.

Lemma arg_length_order_wf: well_founded arg_length_order.
Proof.
  cbv [well_founded]; intros.
  eapply arg_length_order_wf'.
  eauto.
Defined.

Fixpoint insert_rightmost_tt (ty: Kind): structure ty (insert_rightmost_unit ty).
Proof.
  intros.
  destruct ty.
  exact (Second (insert_rightmost_tt ty2)).
  exact Id.
  exact (@Uncancelr Bit).
  exact (@Uncancelr (Vector n ty)).
Defined.

Fixpoint insert_rightmost_tt1 (ty: Kind): structure (remove_rightmost_unit ty) ty.
Proof.
  refine (Fix arg_length_order_wf (fun ty => structure (remove_rightmost_unit ty) ty )
    (fun (ty:Kind)
      (insert_rightmost_tt1': forall ty', arg_length_order ty' ty -> structure (remove_rightmost_unit ty') ty') =>
        match ty as sty return ty=sty -> structure (remove_rightmost_unit sty) sty with
        | Tuple _ Unit => fun _ => Uncancelr
        | Tuple _ ty2 => fun H => (Second (insert_rightmost_tt1' ty2 _ ))
        | _ => fun _ => Id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.

Fixpoint remove_rightmost_tt (ty: Kind): structure ty (remove_rightmost_unit ty).
  refine (Fix arg_length_order_wf (fun ty => structure ty (remove_rightmost_unit ty))
    (fun (ty:Kind)
      (remove_rightmost_tt': forall ty', arg_length_order ty' ty -> structure ty' (remove_rightmost_unit ty')) =>
        match ty as sty return ty=sty -> structure sty (remove_rightmost_unit sty) with
        | Tuple _ Unit => fun _ => Cancelr
        | Tuple _ ty2 => fun H => (Second (remove_rightmost_tt' ty2 _ ))
        | _ => fun _ => Id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.
