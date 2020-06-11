Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.

From Coq Require Import NArith.

Section Vars.
  Context {var: Kind -> Kind -> Type}.

  (* `kappa_sugared` includes constructors for 
    - Kappa Calculus, 
    - the Cava methods, 
    - lifting any morphism from the Constructive arrow instance, 
    - and miscellaneous methods 

    The kappa calculus and LiftMorphism constructors are the only 5 
    "primitive"/required constructors, the rest are a to help syntax 
    or type inference and desugar simply to combinations of the others.
    *)
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
    (* TODO: enable lut *)
    (*| Lut n: (bool^^n --> bool) -> bitvec (N.of_nat n) ~> bit;*)
    | IndexVec: forall n {o}, kappa_sugared << Vector n o, Vector (N.log2_up n) Bit, Unit >> o
    | ToVec: forall {o}, kappa_sugared << o, Unit >> (Vector 1 o)
    | Concat: forall n {o}, kappa_sugared << Vector n o, o, Unit >> (Vector (n+1) o).

  Bind Scope constructive_scope with kappa_sugared.
  Delimit Scope constructive_scope with kappa_sugared.

  (* Everything not manipulation a variable is mapped to its arrow representation via DArr.
  So after desugaring the type is much simpler *)
  Inductive kappa : Kind -> Kind -> Type :=
    | DVar : forall {x y},   var x y -> kappa x y
    | DAbs : forall {x y z}, (var Unit x -> kappa y z) -> kappa << x, y >> z
    | DApp : forall {x y z}, kappa << x, y >> z -> kappa Unit x -> kappa y z
    | DCompose : forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | DArr : forall {x y},   morphism x y -> kappa x y.
End Vars.

Definition Kappa_sugared i o := forall var, @kappa_sugared var i o.
Definition Kappa i o := forall var, @kappa var i o.

Definition kappa_app {var o} i (m: remove_rightmost_unit i ~> o) : @kappa var i o := DCompose (DArr m) (DArr (remove_rightmost_tt _)).

Definition remove_second {x y}: structure << x, y >> x := (Compose Cancelr (Second Drop)).
Definition remove_first {x y}: structure << x, y >> y := (Compose Cancell (First Drop)).

Definition tuple_left {var x y}: @kappa var << <<x, y>> , Unit>> x
  := DArr (Compose remove_second Cancelr).
Definition tuple_right {var x y}: @kappa var << <<x, y>>, Unit>> y
  := DArr (Compose remove_first Cancelr).

Fixpoint desugar {var i o} (e: @kappa_sugared var i o) : @kappa var i o :=
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

  | Constant b => DArr (constant b)
  | ConstantVec v => DArr (constant_bitvec _ v)

  | IndexVec n => kappa_app << Vector n _, Vector (N.log2_up n) Bit, Unit >> (index_vec n _)
  | ToVec => kappa_app << _, Unit >> (to_vec _)
  | Concat n => kappa_app << Vector n _, _, Unit >> (concat n _)
  end.

Definition tupleHelper {var X Y} x y :=  App (App (@MakeTuple var X Y) x) y.
Definition Desugar {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

Hint Resolve Desugar : core.
Hint Resolve desugar : core.