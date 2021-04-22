Require Import Coq.Strings.String.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.letexists.
Require Import Coq.setoid_ring.Ring.

Ltac subst1_map m :=
  match m with
  | map.put ?m _ _ => subst1_map m
  | ?m => is_var m; subst m
  end.

Ltac subst_lets_in t :=
  repeat match goal with
         | x := _ |- _ =>
                lazymatch t with
                | context [x] => subst x
                end
         end.

Ltac ring_simplify_load_addr :=
  repeat lazymatch goal with
         | |- Memory.load _ _ ?addr = _ =>
           progress subst_lets_in addr
         end;
  lazymatch goal with
  | |- Memory.load _ _ ?addr = _ =>
    ring_simplify addr
  end.

Ltac ring_simplify_store_addr :=
  repeat lazymatch goal with
         | |- store _ _ ?addr _ _ => progress subst_lets_in addr
         end;
  lazymatch goal with
  | |- store _ _ ?addr _ _ => ring_simplify addr
  end.

Ltac map_lookup :=
  repeat lazymatch goal with
         | |- context [map.get ?l] =>
           try apply map.get_put_same; try eassumption;
           subst1_map l;
           rewrite ?map.get_put_diff by congruence
         end.

Ltac straightline_with_map_lookup :=
  match goal with
  | _ => straightline
  | |- store _ _ _ _ _ => ring_simplify_store_addr
  | |- exists v, map.get _ _ = Some v /\ _ =>
    eexists; split; [ solve [map_lookup] | ]
  | |- exists v, Memory.load _ _ _ = Some v /\ _ =>
    eexists; split; [ solve [try ring_simplify_load_addr;
                             repeat straightline] | ]
  end.

Ltac one_goal_or_solved t :=
  solve [t] || (t; [ ]).

Ltac invert_nobranch' H t :=
  first [ inversion H; clear H; subst; solve [t]
        | inversion H; clear H; subst; t; [ ] ].
Ltac invert_nobranch H :=
  invert_nobranch' H ltac:(try congruence).

Ltac invert_bool :=
  lazymatch goal with
  | H : (_ && _)%bool = true |- _ =>
    apply Bool.andb_true_iff in H; destruct H
  | H : (_ && _)%bool = false |- _ =>
    apply Bool.andb_false_iff in H; destruct H
  | H : negb _ = true |- _ =>
    apply Bool.negb_true_iff in H
  | H : negb _ = false |- _ =>
    apply Bool.negb_false_iff in H
  end.

(* tactic copied from bedrock2Examples/lightbulb.v *)
Ltac split_if :=
  lazymatch goal with
    |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
        lazymatch c with
        | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
        end
  end.
