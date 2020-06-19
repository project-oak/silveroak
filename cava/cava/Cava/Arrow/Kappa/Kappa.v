Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.

From Coq Require Import Arith NArith Lia NaryFunctions.

Section Vars.
  Context {var: Kind -> Kind -> Type}.

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

    (* Lift any morphism from ConstructiveCat *)
    | LiftMorphism: forall {x y},    morphism x y -> kappa_sugared x y

    (* Helper syntax *)
    | Let: forall {x y z},  kappa_sugared Unit x -> (var Unit x -> kappa_sugared y z) -> kappa_sugared y z
    | TupleLeft: forall {x y}, kappa_sugared << << x, y >>, Unit >> x
    | TupleRight: forall {x y}, kappa_sugared << << x, y >>, Unit >> y
    | MakeTuple: forall {x y}, kappa_sugared << x, y, Unit >> << x, y >>
      
    (* Cava routines *)
    | Constant: bool -> kappa_sugared Unit Bit
    | ConstantVec: forall {n}, N -> kappa_sugared Unit (Vector n Bit)
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
    | Append: forall n {o}, kappa_sugared << Vector n o, o, Unit >> (Vector (n+1) o)
    | Concat: forall n m {o}, kappa_sugared << Vector n o, Vector m o, Unit >> (Vector (n + m) o)
    | Split: forall n m {o}, (m < n) -> kappa_sugared << Vector n o, Unit >> <<Vector m o, Vector (n - m) o>>.

  Bind Scope kind_scope with kappa_sugared.
  Delimit Scope kind_scope with kappa_sugared.


  (* Everything not manipulation a variable is mapped to its arrow representation via DArr.
  So after desugaring the type is much simpler *)
  Inductive kappa : Kind -> Kind -> Type :=
    | DVar : forall {x y},   var x y -> kappa x y
    | DAbs : forall {x y z}, (var Unit x -> kappa y z) -> kappa << x, y >> z
    | DApp : forall {x y z}, kappa << x, y >> z -> kappa Unit x -> kappa y z
    | DCompose : forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | DArr : forall {x y},   morphism x y -> kappa x y.

  Definition kappa_app {o} i (m: remove_rightmost_unit i ~> o) : kappa i o := DCompose (DArr m) (DArr (remove_rightmost_tt _)).

  Definition remove_second {x y}: structure << x, y >> x := (Compose Cancelr (Second Drop)).
  Definition remove_first {x y}: structure << x, y >> y := (Compose Cancell (First Drop)).

  Definition tuple_left {x y}: kappa << <<x, y>> , Unit>> x
    := DArr (Compose remove_second Cancelr).
  Definition tuple_right {x y}: kappa << <<x, y>>, Unit>> y
    := DArr (Compose remove_first Cancelr).

  Definition kappa_to_vec {o} (e: kappa_sugared Unit o)
    : kappa_sugared Unit (Vector 1 o) :=
    App ToVec e.

  Definition tupleHelper {X Y}
    (x: kappa_sugared Unit X)
    (y: kappa_sugared Unit Y) := 
    App (App MakeTuple x) y.

  Definition kappa_append {n o}
    (e1: kappa_sugared Unit (Vector n o))
    (e2: kappa_sugared Unit o)
    : kappa_sugared <<Unit>> (Vector (n+1) o) :=
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
    kappa_index_vec array (ConstantVec index).

  Definition kappa_head {n o}
    (array: kappa_sugared Unit (Vector (S (S n)) o))
    : kappa_sugared Unit <<o, Vector (S n)o>>.
    refine (
    let circuit := (App (Split (S (S n)) 1 _) array) in
    let head_ := Let (App TupleLeft circuit) (fun x => kappa_const_index_vec (Var x) 1) in
    let tail_ := Let (App TupleRight circuit) (fun x => Var x) in
    _).
    assert ((S (S n)) - 1 = S n).
    simpl. auto.
    rewrite H in tail_.
    exact ( tupleHelper head_ tail_ ).
    Grab Existential Variables.
    compute.
    auto.
    apply le_n_S.
    apply le_n_S.
    apply le_0_n.
  Defined.
  Definition kappa_head' {n o}
    : kappa_sugared << Vector (S (S n)) o, Unit>> <<o, Vector (S n) o>>
    := Abs (fun x => kappa_head (Var x)).

  Fixpoint desugar {i o} (e: kappa_sugared i o) : kappa i o :=
    match e with
    | Var x => DVar x
    | Abs f => DAbs (fun x => desugar (f x))
    | App e1 e2 => DApp (desugar e1) (desugar e2)
    | Com f g => DCompose (desugar f) (desugar g)
    | Let x f => DApp (DAbs (fun x => desugar (f x))) (desugar x)
    | LiftMorphism m => DArr m

    | TupleLeft  => tuple_left
    | TupleRight  => tuple_right

    | MakeTuple => DArr (Second Cancelr)

    | Not  => kappa_app << Bit, Unit >> not_gate
    | And  => kappa_app << Bit, Bit, Unit >> and_gate
    | Nand => kappa_app << Bit, Bit, Unit >> nand_gate
    | Or   => kappa_app << Bit, Bit, Unit >> or_gate
    | Nor  => kappa_app << Bit, Bit, Unit >> nor_gate
    | Xor  => kappa_app << Bit, Bit, Unit >> xor_gate
    | Xnor => kappa_app << Bit, Bit, Unit >> xnor_gate
    | Buf  => kappa_app << Bit, Unit >> buf_gate

    | Delay  => DArr (Compose delay_gate Cancelr)

    | Xorcy  => kappa_app << Bit, Bit, Unit >> xorcy 
    | Muxcy  => kappa_app << Bit, Tuple Bit Bit, Unit >> muxcy 
    | UnsignedAdd a b c => kappa_app << Vector a Bit, Vector b Bit, Unit >> (unsigned_add a b c)
    | Lut n f => kappa_app << Vector n Bit, Unit >> (lut n f)

    | Constant b => DArr (constant b)
    | ConstantVec v => DArr (constant_bitvec _ v)

    | IndexVec n => 
      kappa_app << Vector n _, Vector (log2_up_min_1 n) Bit, Unit >> (index_vec n _)
    | SliceVec n x y H1 H2 => 
      kappa_app << Vector n _, Unit >> (slice_vec n x y _ H1 H2)

    | ToVec => kappa_app << _, Unit >> (to_vec _)
    | Append n => kappa_app << Vector n _, _, Unit >> (append n _)
    | Concat n m => kappa_app << Vector n _, Vector m _, Unit >> (concat n m _)
    | Split n m H => kappa_app << Vector n _, Unit >> (split n m _ H)
    end.
End Vars.

Arguments kappa_sugared : clear implicits.
Arguments kappa : clear implicits.

Definition Kappa_sugared i o := forall var, kappa_sugared var i o.
Definition Kappa i o := forall var, kappa var i o.

Definition Desugar {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

Hint Resolve Desugar : core.
Hint Resolve desugar : core.
