Require Import Coq.Strings.String.
Require Import Ltac2.Ltac2.

Ltac2 rec int_to_bits_rec(powers: int list)(val: int) :=
  match powers with
  | p :: rest => if Int.le p val
                 then true :: int_to_bits_rec rest (Int.sub val p)
                 else false :: int_to_bits_rec rest val
  | [] => []
  end.

Ltac2 char_to_bits(c: char) :=
  int_to_bits_rec [128; 64; 32; 16; 8; 4; 2; 1] (Char.to_int c).

Ltac2 bool_to_coq(b: bool) :=
  if b then constr:(true) else constr:(false).

Ltac2 mkApp(f: constr)(args: constr array) :=
  Constr.Unsafe.make (Constr.Unsafe.App f args).

Ltac2 char_to_ascii(c: char) :=
  mkApp constr:(Ascii.Ascii)
        (Array.of_list (List.rev (List.map bool_to_coq (char_to_bits c)))).

Ltac2 rec string_to_coq_rec(s: string)(i: int)(acc: constr) :=
  if Int.lt i 0 then acc else
    let c := char_to_ascii (String.get s i) in
    string_to_coq_rec s (Int.sub i 1) constr:(String.String $c $acc).

Ltac2 string_to_coq(s: string) :=
  string_to_coq_rec s (Int.sub (String.length s) 1) constr:(String.EmptyString).

(* Test: Ltac2 Eval string_to_coq "hello world". *)
