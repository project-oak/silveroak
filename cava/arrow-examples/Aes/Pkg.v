Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

From Coq Require Import NArith Lia.

Import KappaNotation.

Require Import Util List.

Section var.
Variable var: Kind -> Kind -> Type.

(* typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e; *)
Definition CIPH_FWD {n} : kappa_sugared var Unit (Vector n Bit) := <[ #0 ]>.
Definition CIPH_INV {n} : kappa_sugared var Unit (Vector n Bit) := <[ #1 ]>.

Fixpoint outer {n}
  : kappa_sugared var <<Bit, Unit>> (Vector (S n) Bit) := 
match n with
| 0 => <[ \x => mkVec (x) ]>
| S n => <[ \x => x :: !outer x ]>
end.

Definition aes_mvm_acc
  : kappa_sugared var <<Vector 8 Bit, Vector 8 Bit, Bit, Unit>> (Vector 8 Bit) := 
  <[\acc mat vec => acc ^ (mat & (!outer vec)) ]>.

Definition aes_mvm: kappa_sugared var <<Vector 8 Bit, Vector 8 (Vector 8 Bit), Unit>> (Vector 8 Bit) :=
  <[\ vec_b mat_a =>
  let _1 = !aes_mvm_acc (#0) (mat_a[#0]) (vec_b[#7]) in
  let _2 = !aes_mvm_acc (_1) (mat_a[#1]) (vec_b[#6]) in
  let _3 = !aes_mvm_acc (_2) (mat_a[#2]) (vec_b[#5]) in
  let _4 = !aes_mvm_acc (_3) (mat_a[#3]) (vec_b[#4]) in
  let _5 = !aes_mvm_acc (_4) (mat_a[#4]) (vec_b[#3]) in
  let _6 = !aes_mvm_acc (_5) (mat_a[#5]) (vec_b[#2]) in
  let _7 = !aes_mvm_acc (_6) (mat_a[#6]) (vec_b[#1]) in
  let _8 = !aes_mvm_acc (_7) (mat_a[#7]) (vec_b[#0]) in
  _8
  ]>.

End var.


Arguments aes_mvm {var}. 
Arguments outer {var}. 
Arguments CIPH_FWD {var n}. 
Arguments CIPH_INV {var n}. 