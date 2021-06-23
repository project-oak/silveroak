Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Local Open Scope Z_scope.

Section WithParameters.
  Context {width: Z}
          {word: word width}
          {mem: map.map word Byte.byte}
          {locals: map.map String.string word}
          {env : map.map String.string (list String.string * list String.string * cmd)}.

  Local Notation trace := (list (mem * String.string * list word * (mem * list word))).
  Local Notation ExtSpec :=
    (trace -> mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop).

  Context (espec1 espec2: ExtSpec).

  Definition ext_spec_extends := forall t m action args post,
      espec2 t m action args post -> espec1 t m action args post.

  Instance semantics_params1: Semantics.parameters := {
    ext_spec := espec1;
  }.

  Instance semantics_params2: Semantics.parameters := {
    ext_spec := espec2;
  }.

  Local Hint Constructors exec.exec : core.
  Local Hint Extern 1 (@ext_spec _ _ _ _ _ _) => (progress cbn); unfold ext_spec_extends in * : core.

  Hypothesis espec1_extends_expec2: ext_spec_extends.

  Lemma run_with_extended_ext_spec: forall e c t m l mc post,
      exec (pp := semantics_params2) e c t m l mc post ->
      exec (pp := semantics_params1) e c t m l mc post.
  Proof. induction 1; eauto. Qed.
End WithParameters.
