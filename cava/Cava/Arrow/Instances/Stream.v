Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Lists.Streams.

From Coq Require Import btauto.Btauto.

Require Import Cava.Arrow.Arrow.

Set Implicit Arguments.

Section CoqStreamEval.
  Instance CoqStreamCat : Category := {
    morphism X Y := Stream X -> Stream Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqStreamArr : Arrow := {
    unit := Datatypes.unit : Type;

    fork _ _ _ f g := fun xs => zipWith pair (f xs) (g xs);
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

  Instance CoqStreamCava : Cava := {
    bit := bool;

    fromBool b := fun _ => liftBool b;

    not_gate := map (fun b => negb b);
    and_gate := map (fun xy => andb (fst xy) (snd xy));
  }.
End CoqStreamEval.
