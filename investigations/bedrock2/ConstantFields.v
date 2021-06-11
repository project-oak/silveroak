Require Import Bedrock2Experiments.Ltac2StringToCoq.
Require Import Ltac2.Ltac2. Require Ltac2.Option.
Require Import Coq.Strings.Ascii Coq.Strings.String.

(* puts parentheses around each occurrence of the char 0 *)
Ltac2 rec parenthesize_trailing_0(s: constr) :=
  lazy_match! s with
  | EmptyString => constr:(String.EmptyString)
  | String ?c ?rest =>
    lazy_match! rest with
    | EmptyString => if Constr.equal c constr:("0"%char) then constr:("(0)"%string) else s
    | String _ _ => let rest' := parenthesize_trailing_0 rest in constr:(String $c $rest')
    end
  end.

(* Test: Ltac2 Eval parenthesize_trailing_0 constr:("a 0_b00..00"%string). *)

Ltac2 rec binder_names(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b body =>
    Option.get (Constr.Binder.name b) :: binder_names body
  | _ => []
  end.

Ltac2 unapp(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f a => (f, a)
  | _ => (c, Array.empty ())
  end.

(* given a goal which is a record, instantiate each field with (f QUALI NAME),
   where NAME is the name of that field, and QUALI is the qualification (list of
   idents) needed in front of NAME to get a fully qualified name *)
Ltac2 instantiate_record_based_on_fieldnames(f: ident list -> ident -> constr) :=
  lazy_match! goal with
  | [ |- ?g ] =>
    let (r, rargs) := unapp g in
    match Constr.Unsafe.kind r with
    | Constr.Unsafe.Ind ind inst =>
      let ctor_ref := Std.ConstructRef (Constr.Unsafe.constructor ind 0) in
      let ctor_trm := Env.instantiate ctor_ref in
      let ctor_type := Constr.type ctor_trm in
      let field_names := List.skipn (Array.length rargs) (binder_names ctor_type) in
      let qualification := List.removelast (Env.path ctor_ref) in
      let args := List.map (f qualification) field_names in
      let res := mkApp ctor_trm (Array.append rargs (Array.of_list args)) in
      exact $res
    | _ => Control.throw
             (Tactic_failure (Some (Message.of_string "goal is not an inductive")))
    end
  end.

Ltac instantiate_record_with_fieldname_vars :=
  ltac2:(instantiate_record_based_on_fieldnames
           (fun q i => parenthesize_trailing_0 (string_to_coq (Ident.to_string i)))).

(* instantiate the goal with a record where each field is instantiated by applying f *)
Ltac2 map_record_fields(f: constr) :=
  instantiate_record_based_on_fieldnames (fun q i =>
     let getter := Env.instantiate (Option.get (Env.get (List.append q [i]))) in
     constr:($f ($getter _ _))).

Ltac map_record_fields :=
  ltac2:(f |- map_record_fields (Option.get (Ltac1.to_constr f))).
