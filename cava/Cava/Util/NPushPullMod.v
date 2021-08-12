Require Import Coq.NArith.NArith.
Local Open Scope N_scope.

(* Based on coqutil.Z.PushPullMod *)
(* TODO: upstream this to coqutil? *)
Module N.

  Lemma mod_0_r (a : N) : a mod 0 = a.
  Proof. destruct a; reflexivity. Qed.

  Lemma add_mod_full (a b m : N) : (a + b) mod m = (a mod m + b mod m) mod m.
  Proof.
    destruct (N.eq_dec m 0); [ | solve [auto using N.add_mod] ].
    subst. rewrite !N.mod_0_r; reflexivity.
  Qed.

  Lemma mul_mod_full (a b m : N) : (a * b) mod m = (a mod m * (b mod m)) mod m.
  Proof.
    destruct (N.eq_dec m 0); [ | solve [auto using N.mul_mod] ].
    subst. rewrite !N.mod_0_r; reflexivity.
  Qed.

  Lemma mod_mod_full (a m : N) : (a mod m) mod m = a mod m.
  Proof.
    destruct (N.eq_dec m 0); [ | solve [auto using N.mod_mod] ].
    subst. rewrite !N.mod_0_r; reflexivity.
  Qed.

  Ltac push_mod_step :=
    match goal with
    | |- context [ (?op ?a ?b) mod ?m ] =>
      lazymatch a with
      | _ mod m =>
        lazymatch b with
        | _ mod m => fail
        | _ => idtac
        end
      | _ => idtac
      end;
      match op with
      | N.add => rewrite (add_mod_full a b m)
      | N.mul => rewrite (mul_mod_full a b m)
      end
    end.

  Ltac push_mod := repeat push_mod_step.

  Ltac mod_free t :=
    lazymatch t with
    | N.modulo ?a ?b => fail "contains" a "mod" b
    | N.add ?a ?b => mod_free a; mod_free b
    | N.mul ?a ?b => mod_free a; mod_free b
    | _ => idtac
    end.

  Ltac pull_mod_step :=
    match goal with
    | |- context [ (?op (?a mod ?m) (?b mod ?m)) mod ?m ] =>
      mod_free a;
      mod_free b;
      match op with
      | N.add => rewrite <- (add_mod_full a b m)
      | N.mul => rewrite <- (mul_mod_full a b m)
      end
    end.

  Ltac pull_mod := repeat pull_mod_step.

  Ltac push_pull_mod :=
    push_mod;
    rewrite? mod_mod_full;
    pull_mod.

  Ltac mod_equality :=
    push_pull_mod;
    solve [repeat (ring || f_equal)].

End N.
