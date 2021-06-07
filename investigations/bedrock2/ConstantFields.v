Require Import Bedrock2Experiments.Ltac2StringToCoq.
Require Import Ltac2.Ltac2. Require Ltac2.Option.

Ltac2 rec binder_names(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b body =>
    Ident.to_string (Option.get (Constr.Binder.name b)) :: binder_names body
  | _ => []
  end.

(* given a goal which is a record whose fields all are of type expr,
   instantiate each field with (expr.var NAME), where NAME is the
   name of that field *)
Ltac2 instantiate_record_with_fieldname_vars () :=
  lazy_match! goal with
  | [ |- ?r ?t ] =>
    match Constr.Unsafe.kind r with
    | Constr.Unsafe.Ind ind inst =>
      let ctor_ref := Std.ConstructRef (Constr.Unsafe.constructor ind 0) in
      let ctor_trm := Env.instantiate ctor_ref in
      let ctor_type := Constr.type ctor_trm in
      let field_names := List.tl (binder_names ctor_type) in
      let args := constr:(String.string) :: List.map string_to_coq field_names in
      let res := mkApp ctor_trm (Array.of_list args) in
      exact $res
    | _ => Control.throw
             (Tactic_failure (Some (Message.of_string "goal is not an inductive")))
    end
  end.

Ltac instantiate_record_with_fieldname_vars :=
  ltac2:(instantiate_record_with_fieldname_vars ()).
