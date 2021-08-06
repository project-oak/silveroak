Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SortedListString.
Require Import bedrock2.Syntax.

Instance locals{word: word.word 32}: map.map String.string word := SortedListString.map _.
Instance env: map.map String.string (list String.string * list String.string * cmd) :=
  SortedListString.map _.

Instance locals_ok{word: word.word 32}{word_ok: word.ok word}: map.ok locals := SortedListString.ok _.
Instance env_ok: map.ok env := SortedListString.ok _.

Arguments locals: simpl never.
Arguments env: simpl never.

(* See https://github.com/mit-plv/bedrock2/pull/180,
       https://github.com/mit-plv/bedrock2/issues/193,
       https://github.com/coq/coq/issues/14707 *)
#[global] Hint Mode word.word - : typeclass_instances.
#[global] Hint Mode map.map - - : typeclass_instances.
