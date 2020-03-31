From Coq Require Import Program.Tactics.
From Coq Require Import Vector.
From Coq Require Import Bool.Bool.
From Coq Require Import Bool.Bvector.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Lists.Streams.
From Coq Require Import btauto.Btauto.

From Cava Require Import BitArithmetic.
From Cava Require Import Arrow.Arrow.

Set Implicit Arguments.

Section CoqStreamEval.
  Instance CoqStreamCat : Category := {
    object := Type;
    morphism X Y := Stream X -> Stream Y;
    compose _ _ _ f g x := f (g x);
    id X x := x;
  }.

  Instance CoqStreamArr : Arrow := {
    unit := Datatypes.unit : Type;

    fork _ _ _ f g xs := zipWith pair (f xs) (g xs);
    exl X Y := map fst;
    exr X Y := map snd;

    drop _ := map (fun _ => tt);
    copy _ := map (fun x => pair x x);

    swap _ _ := map (fun x => (snd x, fst x));

    uncancell _ := map (fun x => (tt, x));
    uncancelr _ := map (fun x => (x, tt));

    assoc _ _ _   := map (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)));
    unassoc _ _ _ := map (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)));
  }.

  CoFixpoint liftBool (b: bool) : Stream bool
  := Cons b (liftBool b).
  CoFixpoint liftBvector {n: nat} (v: Bvector n) : Stream (Bvector n)
  := Cons v (liftBvector v).

  Instance CoqStreamCava : Cava := {
    bit := bool;
    bitvec n := Bvector n;

    constant b _ := liftBool b;
    constant_vec _ v _ := liftBvector v;

    not_gate := map (fun b => negb b);
    and_gate := map (fun '(x,y) => andb x y);
    nand_gate := map (fun '(x,y) => negb (andb x y));
    or_gate := map (fun '(x,y) => orb x y);
    nor_gate := map (fun '(x,y) => negb (orb x y));
    xor_gate := map (fun '(x,y) => xorb x y);
    xnor_gate := map (fun '(x,y) => negb (xorb x y));
    buf_gate := map (fun x => x);

    xorcy := map (fun '(x,y) => xorb x y);
    muxcy := map (fun xyz : bool * bool * bool =>
      let '(x,y,z) := xyz in if x then y else z
    );

    unsigned_add m n := map (fun '(av, bv) =>
      let a := bitvec_to_nat av in
      let b := bitvec_to_nat bv in
      let c := a + b in
      nat_to_bitvec (max m n + 1) c
    );
  }.
End CoqStreamEval.
