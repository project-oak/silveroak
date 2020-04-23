Require Import Cava.Arrow.Arrow.

Require Import Nand.

(* An implementation of an XOR gate made out of the NAND circuit
   defined above. *)
Definition xor
  `{Cava}
  : (bit**bit) ~> bit :=
  copy
  >>> first (nand >>> copy)                    (* ((nand,nand),(x,y)) *)
  >>> assoc                                    (* (nand,(nand,(x,y))) *)
  >>> second (unassoc >>> first nand >>> swap) (* (nand,(y, x_nand)) *)
  >>> unassoc >>> first nand                   (* (y_nand,x_nand) *)
  >>> nand.
