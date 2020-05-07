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

From Coq Require Import Setoid.
From Coq Require Import Classes.Morphisms.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

(* TODO: currently disabled
*)

Section CoqStreamEval.
  #[refine] Instance CoqStreamCat : Category := {
    object := Type;
    morphism X Y := Stream X -> Stream Y;
    compose _ _ _ f g x := f (g x);
    id X x := x;

    morphism_equivalence x y f g := forall x, EqSt (f x) (g x);
  }.
  Proof.
    intros.
    apply Build_Equivalence.
    unfold Reflexive. intros. apply EqSt_reflex.
    unfold Symmetric. intros. apply sym_EqSt. apply H. 
    unfold Transitive. intros. 
    pose proof (trans_EqSt (H x1) (H0 x1)).
    auto.

    intros.
    unfold Proper. 
    refine (fun f => _). intros.
    refine (fun g => _). intros.


    setoid_rewrite associativity in H.
    f_equal.

    specialize (H0 x0).
    pose (g x0).
    pose proof (H s).
    pose (y1 x0).
    pose proof (H s0).

    change (EqSt (f (g x0)) (y0 (y1 x0))).


    cofix G.
    destruct x0 as [x' xs].
    simpl.

    apply G.


    intros. apply EqSt_reflex.
    intros. apply EqSt_reflex.
    intros. apply EqSt_reflex.
  Defined.

  #[refine] Instance CoqStreamArr : Arrow := {
    unit := Datatypes.unit : Type;

    (* fork _ _ _ f g xs := zipWith pair (f xs) (g xs); *)

    first _ _ _ f xs := zipWith pair (f (map fst xs)) (map snd xs);
    second _ _ _ f xs := zipWith pair (map fst xs) (f (map snd xs));

    exl X Y := map fst;
    exr X Y := map snd;

    drop _ := map (fun _ => tt);
    copy _ := map (fun x => pair x x);

    swap _ _ := map (fun x => (snd x, fst x));

    uncancell _ := map (fun x => (tt, x));
    uncancelr _ := map (fun x => (x, tt));

    assoc _ _ _   := map (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)));
    unassoc _ _ _ := map (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)));

    (* laws *)

    (* obj_equiv x y := 
      (sigx (x~>y) (y~>x) (fun f g => 
      f >>> g =M= id /\
      g >>> f =M= id
      ));

    exl_unit_uncancelr x := @exl x unit >>> uncancelr =M= id;
    exr_unit_uncancell x := @exr unit x >>> uncancell =M= id;
    uncancelr_exl x := uncancelr >>> @exl x unit =M= id;
    uncancell_exr x := uncancell >>> @exr unit x =M= id;

    exl_unit x : obj_equiv (x**unit) x;
    prefix_equiv x y : obj_equiv x y -> forall a, obj_equiv (a**x) (a**y); *)
  }.
  Proof.
    intros.
    assert (H:
      (fun (f : (x * Datatypes.unit)%type ~[ CoqStreamCat ]~> x)
        (g : x ~[ CoqStreamCat ]~> (x * Datatypes.unit)%type) =>
        f >>> g =M= id /\ g >>> f =M= id) (map fst)
        (fun xs : Stream x => zipWith pair xs (const tt))
      ).
    split.
    simpl.
    extensionality z.
    unzip 
    cofix G.

    admit.
    exact (existx _ _ _ (map fst) (fun xs => zipWith pair xs (const tt)) H).


  Instance CoqStreamCava : Cava := {
    bit := bool;
    bitvec n := Bvector n;

    constant b _ := const b;
    constant_vec _ v _ := const v;

    not_gate := map (fun b => negb b);
    and_gate := map (fun '(x,y) => andb x y);
    nand_gate := map (fun '(x,y) => negb (andb x y));
    or_gate := map (fun '(x,y) => orb x y);
    nor_gate := map (fun '(x,y) => negb (orb x y));
    xor_gate := map (fun '(x,y) => xorb x y);
    xnor_gate := map (fun '(x,y) => negb (xorb x y));
    buf_gate := map (fun x => x);

    xorcy := map (fun '(x,y) => xorb x y);
    muxcy := map (fun xyz : bool * (bool * bool) =>
      let '(x,(y,z)) := xyz in if x then y else z
    );

    unsigned_add m n s := map (fun '(av, bv) =>
      let a := bitvec_to_nat av in
      let b := bitvec_to_nat bv in
      let c := a + b in
      nat_to_bitvec_sized s c
    );
  }.
End CoqStreamEval.
