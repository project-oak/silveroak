Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Word.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* read and write interaction names *)
Definition READ := "MMIOREAD".
Definition WRITE := "MMIOWRITE".

(* Core class : defines all the constants *)
Class constants T :=
  { VALUE_ADDR : T;
    STATUS_ADDR : T;
    STATUS_DONE : T }.

(* Given the string names of all the constants, coerce them to bedrock2
   expressions with expr.var *)
Definition constant_vars
           {names : constants string}
  : constants expr :=
  {| VALUE_ADDR := expr.var VALUE_ADDR;
     STATUS_ADDR := expr.var STATUS_ADDR;
     STATUS_DONE := expr.var STATUS_DONE;
  |}.

(* Given the Z values of all the constants, convert them to exprs with
   expr.literal *)
Definition constant_literals
           {vals : constants Z}
  : constants expr :=
  {| VALUE_ADDR := expr.literal VALUE_ADDR;
     STATUS_ADDR := expr.literal STATUS_ADDR;
     STATUS_DONE := expr.literal STATUS_DONE;
  |}.

(* Given the Z values of all the constants, convert them to words with
   word.of_Z *)
Definition constant_words
           {width} {word : word width} {word_ok : word.ok word}
           {vals : constants Z}
  : constants word :=
  {| VALUE_ADDR := word.of_Z VALUE_ADDR;
     STATUS_ADDR := word.of_Z STATUS_ADDR;
     STATUS_DONE := word.of_Z STATUS_DONE;
  |}.

(* This instance provide the string name for each constant *)
Definition constant_names : constants string :=
  {| VALUE_ADDR := "VALUE_ADDR";
     STATUS_ADDR := "STATUS_ADDR";
     STATUS_DONE := "STATUS_DONE";
  |}.

(* This list includes all the constants and is prepended to functions' argument
   lists to initialize their environment *)
Definition globals {T} {consts : constants T} : list T :=
  [ VALUE_ADDR
    ; STATUS_ADDR
    ; STATUS_DONE
  ].

(* All register addresses *)
Definition reg_addrs {width} {word : word.word width}
           {global_values : constants word}
  : list word.rep := [VALUE_ADDR (*; STATUS_ADDR <-- same addr as VALUE_ADDR, using bit 31 *)].

(* This class includes all the properties the constants must satisfy *)
Class constants_ok
      {width} {word : word width} {word_ok : word.ok word}
      (global_values : constants word) :=
  { addrs_unique : NoDup reg_addrs;
    addrs_aligned :
      Forall (fun w => word.unsigned w mod 4 = 0) reg_addrs;
    addrs_small :
      Forall (fun w => word.unsigned w + 4 < 2 ^ 32) reg_addrs;
    status_flags_unique_and_nonzero :
      NoDup
        ((word.of_Z 0)
           :: (map (fun flag_position => word.slu (word.of_Z 1) flag_position)
                  [STATUS_DONE]));
    flags_lt_width : Forall (fun w => word.unsigned w < width)
                            [STATUS_DONE]
  }.
