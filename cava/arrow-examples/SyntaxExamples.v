Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Instances.Combinational.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Coq Require Import Lists.List.
Import ListNotations.

Section definition.
  Import KappaNotation. 

  Variable var: Kind -> Kind -> Type.

  Definition xilinxFullAdder
    : kappa_sugared var << Bit, << Bit, Bit >>, Unit >> << Bit, Bit >> :=
    <[ \ cin ab =>
      let '(a,b) = ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.
End definition.

Definition xilinxFullAdder_structure := (ltac: (build_structure xilinxFullAdder)).

Lemma xilinxFullAdder_is_combinational: wf_combinational (toCava xilinxFullAdder_structure _).
Proof. combinational_obvious. Qed.
