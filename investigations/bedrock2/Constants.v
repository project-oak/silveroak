Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.

Module constant.
  (* Typeclass for constant values *)
  Definition constant (name : string) : Type := Z.
  Existing Class constant.

  (* Typeclass for functions that convert a constant to a bedrock2 expression *)
  Definition interp : Type := forall name, constant name -> expr.expr.
  Existing Class interp.

  (* Use `Existing Instance constants.var_interp` to interpret constants as
     named variables -- useful for printing C that will use those constants *)
  Definition var_interp : interp := fun name _ => expr.var name.

  (* Use `Existing Instance constants.literal_interp` to interpret constants as
     literals -- useful for proofs *)
  Definition literal_interp : interp := fun _ => expr.literal.
End constant.
Notation constant := constant.constant.
