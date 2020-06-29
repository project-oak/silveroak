From Arrow Require Import Category Arrow Kappa ClosureConversion.
Require Import Cava.Arrow.Arrow.

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Open Scope category_scope.
Open Scope arrow_scope.

Section Vars.
  Context {var: Kind -> Kind -> Type}.

  Definition lift_constant (ty: Kind): Type :=
    match ty with
    | Bit => bool
    | Vector n Bit => N
    | _ => False
    end.

  (*
    `kappa_sugared` includes constructors for
    - Kappa Calculus,
    - the Cava methods,
    - lifting any morphism from the Constructive arrow instance,
    - and miscellaneous methods

    The kappa calculus and LiftMorphism constructors are the only 5
    "primitive"/required constructors, the rest are a to help syntax
    or type inference and desugar simply to combinations of the others.
    *)
  (* TODO: cleanup / have a more modular EDSL representation *)
  Inductive kappa_sugared : Kind -> Kind -> Type :=
    (* Kappa Calculus *)
    | Var: forall {x y},    var x y -> kappa_sugared x y
    | Abs: forall {x y z},  (var Unit x -> kappa_sugared y z) -> kappa_sugared << x, y >> z
    | App: forall {x y z},  kappa_sugared << x, y >> z -> kappa_sugared Unit x -> kappa_sugared y z
    | Com: forall {x y z},  kappa_sugared y z -> kappa_sugared x y -> kappa_sugared x z

    (* Helper syntax *)
    | Let: forall {x y z},  kappa_sugared Unit x -> (var Unit x -> kappa_sugared y z) -> kappa_sugared y z
    | Fst: forall {x y}, kappa_sugared << << x, y >>, Unit >> x
    | Snd: forall {x y}, kappa_sugared << << x, y >>, Unit >> y
    | Pair: forall {x y}, kappa_sugared << x, y, Unit >> << x, y >>

    (* Cava routines *)
    | LiftConstant: forall {x}, lift_constant x -> kappa_sugared Unit x

    | Not: kappa_sugared << Bit, Unit >> Bit
    | And: kappa_sugared << Bit, Bit, Unit >> Bit
    | Nand: kappa_sugared << Bit, Bit, Unit >> Bit
    | Or:   kappa_sugared << Bit, Bit, Unit >> Bit
    | Nor:  kappa_sugared << Bit, Bit, Unit >> Bit
    | Xor:  kappa_sugared << Bit, Bit, Unit >> Bit
    | Xnor: kappa_sugared << Bit, Bit, Unit >> Bit
    | Buf:  kappa_sugared << Bit, Unit >>      Bit
    | Delay: forall {o}, kappa_sugared << o, Unit >> o
    | Xorcy: kappa_sugared << Bit, Bit, Unit >> Bit
    | Muxcy: kappa_sugared << Bit, Tuple Bit Bit, Unit >> Bit
    | UnsignedAdd: forall a b c, kappa_sugared << Vector a Bit, Vector b Bit, Unit >> (Vector c Bit)

    | Lut n: (bool^^n --> bool) -> kappa_sugared << Vector n Bit, Unit >> Bit
    | IndexVec: forall n {o}, kappa_sugared << Vector n o, Vector (log2_up_min_1 n) Bit, Unit >> o
    | SliceVec: forall n x y {o}, x < n -> y <= x -> kappa_sugared << Vector n o, Unit >> (Vector (x - y + 1) o)
    | ToVec: forall {o}, kappa_sugared << o, Unit >> (Vector 1 o)
    | Append: forall n {o}, kappa_sugared << Vector n o, o, Unit >> (Vector (S n) o)
    | Concat: forall n m {o}, kappa_sugared << Vector n o, Vector m o, Unit >> (Vector (n + m) o)
    | Split: forall n m {o}, (m <= n) -> kappa_sugared << Vector n o, Unit >> <<Vector m o, Vector (n - m) o>>.

  Bind Scope kind_scope with kappa_sugared.
  Delimit Scope kind_scope with kappa_sugared.

(* 
  Definition kappa_app {o} i (m: i ~> o) : kappa (insert_rightmost_unit i) o := DCompose (DArr m) (DArr (remove_rightmost_tt _)).

  Definition remove_second {x y}: structure << x, y >> x := (Compose Cancelr (Second Drop)).
  Definition remove_first {x y}: structure << x, y >> y := (Compose Cancell (First Drop)).

  Definition tuple_left {x y}: kappa << <<x, y>> , Unit>> x
    := DArr (Compose remove_second Cancelr).
  Definition tuple_right {x y}: kappa << <<x, y>>, Unit>> y
    := DArr (Compose remove_first Cancelr). *)

  Definition kappa_to_vec {o} (e: kappa_sugared Unit o)
    : kappa_sugared Unit (Vector 1 o) :=
    App ToVec e.

  Definition tupleHelper {X Y}
    (x: kappa_sugared Unit X)
    (y: kappa_sugared Unit Y) :=
    App (App Pair x) y.

  Definition kappa_append {n o}
    (e1: kappa_sugared Unit (Vector n o))
    (e2: kappa_sugared Unit o)
    : kappa_sugared <<Unit>> (Vector (S n) o) :=
    let packed := tupleHelper e1 e2 in
    App (App (Append _) e1) e2.

  Definition kappa_index_vec {n o}
    (array: kappa_sugared Unit (Vector n o))
    (index: kappa_sugared Unit (Vector (log2_up_min_1 n) Bit))
    : kappa_sugared Unit o :=
    (App (App (IndexVec n) array) index).

  Definition kappa_slice_vec {n o}
    (array: kappa_sugared Unit (Vector n o))
    (x y: nat)
    (H1: x < n)
    (H2: y <= x)
    : kappa_sugared Unit (Vector (x - y + 1) o) :=
    (App (SliceVec n x y H1 H2) array).

  Definition kappa_const_index_vec {n o}
    (array: kappa_sugared Unit (Vector n o))
    (index: N)
    : kappa_sugared Unit o :=
    kappa_index_vec array (@LiftConstant (Vector _ Bit) index).

  Lemma s_n_sub_1: forall n, {(S n - 1) = n} + {(S n - 1) <> n}.
  Proof.
    decide equality.
  Defined.

  Lemma s_n_sub_1_contra: forall n, (S n - 1) <> n -> False.
  Proof.
    intros.
    simpl in H.
    rewrite Nat.sub_0_r in H.
    destruct H.
    reflexivity.
  Qed.

  Definition kappa_uncons {n o}
    (array: kappa_sugared Unit (Vector (S n) o))
    : kappa_sugared Unit <<o, Vector n o>> :=
    let circuit := (App (Split (S n) 1 (Nat.lt_0_succ n)) array) in
    let head_ := Let (App Fst circuit) (fun x => kappa_const_index_vec (Var x) 0) in
    let tail_ := Let (App Snd circuit) (fun x => Var x) in
    match (s_n_sub_1 n) with
    | left Heq => rew [ fun X => kappa_sugared Unit << o, Vector X o >> ] Heq in tupleHelper head_ tail_ 
    | right Hneq => match s_n_sub_1_contra n Hneq with end
    end.

  Definition kappa_uncons' {n o}
    : kappa_sugared << Vector (S n) o, Unit>> <<o, Vector n o>>
    := Abs (fun x => kappa_uncons (Var x)).

  Arguments Kappa.Var [_ _ _ _ _ var _ _].
  Arguments Kappa.Abs [_ _ _ _ _ var _ _ _].
  Arguments Kappa.App [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Comp [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Morph [_ _ _ _ _ var _ _].
  Arguments Kappa.LetRec [_ _ _ _ _ var _ _ _].

  Definition liftCava `{Cava} i {o} (f: remove_rightmost_unit i ~> o) 
    : kappa var i o :=
    Kappa.Comp (Kappa.Morph f) (Kappa.Morph (remove_rightmost_tt i)).

  Fixpoint desugar {cava: Cava} {i o} (e: kappa_sugared i o) : kappa var i o :=
    match e with
    | Var x => Kappa.Var x
    | Abs f => Kappa.Abs (fun x => desugar (f x))
    | App e1 e2 => Kappa.App (desugar e1) (desugar e2)
    | Com f g => Kappa.Comp (desugar f) (desugar g)
    | Let x f => Kappa.App (Kappa.Abs (fun x => desugar (f x))) (desugar x)

    | Fst  => Kappa.Morph (cancelr >>> second drop >>> cancelr)
    | Snd  => Kappa.Morph (cancelr >>> first drop >>> cancell)

    | Pair => Kappa.Morph (second cancelr)

    | Not  => liftCava <<_,u>> not_gate
    | And  => liftCava <<_,_,u>> and_gate
    | Nand => liftCava <<_,_,u>> nand_gate
    | Or   => liftCava <<_,_,u>> or_gate
    | Nor  => liftCava <<_,_,u>> nor_gate
    | Xor  => liftCava <<_,_,u>> xor_gate
    | Xnor => liftCava <<_,_,u>> xnor_gate
    | Buf  => liftCava <<_,u>> buf_gate

    | Delay  => Kappa.Comp (Kappa.Morph delay_gate) (Kappa.Morph cancelr)

    | Xorcy  => liftCava <<_,_,u>> xorcy
    | Muxcy  => liftCava <<_,_,u>> muxcy
    | UnsignedAdd a b c => liftCava <<_,_,u>> (unsigned_add a b c)
    | Lut n f => liftCava <<_,u>> (lut n f)

    | @LiftConstant ty x =>
      match ty, x with
      | Bit, b => Kappa.Morph (constant b)
      | Vector n Bit, v => Kappa.Morph (constant_bitvec _ v)
      | _, H => match H with end
      end

    | IndexVec n =>
      liftCava <<_,_,u>> (index_vec n _)
    | SliceVec n x y H1 H2 =>
      liftCava <<_,u>> (slice_vec n x y _ H1 H2)

    | ToVec => liftCava <<_,u>> (to_vec _)
    | Append n => liftCava <<_,_,u>> (append n _)
    | Concat n m => liftCava <<_,_,u>> (concat n m _)
    | Split n m H => liftCava <<_,u>> (split n m _ H)
    end.
End Vars.

Arguments kappa_sugared : clear implicits.

Definition Kappa_sugared i o := forall var, kappa_sugared var i o.

Definition Desugar `{Cava} {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

Hint Resolve Desugar : core.
Hint Resolve desugar : core.
