(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

(* Cava implementations of the gates described in the Nand Game website
   which describes how to build circuit components using only NAND gates
   and registers. http://nandgame.com/
*)

From Coq Require Import Bool.Bool. 
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Hask.Control.Monad.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(******************************************************************************)
(* Build a half-adder                                                         *)
(******************************************************************************)

Definition halfAdder {m t} `{Cava m t} a b :=
  partial_sum <- xor_gate [a; b] ;
  carry <- and_gate [a; b] ;
  return_ (partial_sum, carry).

Definition halfAdderTop {m t} `{CavaTop m t} :=
  setModuleName "halfadder" ;;
  a <- inputBit "a" ;
  b <- inputBit "b" ;
  ps_c <- halfAdder a b ;
  outputBit "partial_sum" (fst ps_c) ;;
  outputBit "carry" (snd ps_c).

Definition halfAdderNetlist := makeNetlist halfAdderTop.

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour : forall (a : bool) (b : bool),
                            combinational (halfAdder a b) = (xorb a b, a && b).

Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b.
  all : reflexivity.
Qed.

(* From the original nand *)

Definition p_bit_to_nat(a : bool) : nat := if a then 1 else 0.

Fixpoint p_bits_to_nat(b : list bool) : nat :=
  match b with
    | nil => 0
    | b0::t => p_bit_to_nat b0 + 2 * p_bits_to_nat t
  end.

(* end from *)

(* A proof that the half adder does arithmetic *)
Lemma halfAdder_nat :
  forall (a b : bool),
    let (l, h) := combinational (halfAdder a b) in p_bits_to_nat [l; h] = p_bit_to_nat a + p_bit_to_nat b.
Proof.
  intros.
  case a, b.
  all: reflexivity.
Qed.


(******************************************************************************)
(* Build a full-adder                                                         *)
(******************************************************************************)

Definition fullAdder {m t} `{Cava m t} a b cin :=
  abl_abh <- halfAdder a b ;
  abcl_abch <- halfAdder (fst abl_abh) cin ;
  cout <- or_gate [snd abl_abh; snd abcl_abch] ;
  return_ (fst abcl_abch, cout).

Definition fullAdderTop {m t} `{CavaTop m t} :=
  setModuleName "fulladder" ;;
  a <- inputBit "a" ;
  b <- inputBit "b" ;
  cin <- inputBit "cin" ;
  sum_cout <- fullAdder a b cin ;
  outputBit "sum" (fst sum_cout) ;;
  outputBit "carry" (snd sum_cout).


Definition fullAdderNetlist := makeNetlist fullAdderTop.

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                            combinational (fullAdder a b cin)
                              = (xorb cin (xorb a b),
                                 (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

(* Prove the full adder does arithmetic *)
Lemma fullAdder_nat :
  forall (a b c : bool),
    let (l, h) := combinational (fullAdder a b c) in p_bits_to_nat [l; h] = p_bit_to_nat a + p_bit_to_nat b + p_bit_to_nat c.
Proof.
  intros.
  case a, b, c.
  all: reflexivity.
Qed.

(******************************************************************************)
(* Build a full-adder with explicit use of fast carry                                                        *)
(******************************************************************************)

Definition fullAdderFC {m bit} `{Cava m bit} (cin_ab : bit * (bit * bit))
  : m (bit * bit)%type :=
  let cin := fst cin_ab in
  let ab := snd cin_ab in
  let a := fst ab in
  let b := snd ab in
  part_sum <- xor_gate [a; b] ;
  sum <- xorcy cin part_sum ;
  cout <- muxcy cin a part_sum ;
  return_ (sum, cout).

Definition fullAdderFCTop {m t} `{CavaTop m t} :=
  setModuleName "fulladderFC" ;;
  a <- inputBit "a" ;
  b <- inputBit "b" ;
  cin <- inputBit "cin" ;
  sum_cout <- fullAdderFC (cin, (a, b)) ;
  outputBit "sum" (fst sum_cout) ;;
  outputBit "carry" (snd sum_cout).

Definition fullAdderFCNetlist := makeNetlist fullAdderFCTop.

(* A proof that the the full-adder is correct. *)
Lemma fullAdderFC_behaviour : forall (a : bool) (b : bool) (cin : bool),
                              combinational (fullAdderFC (cin, (a, b)))
                               = (xorb cin (xorb a b),
                                   (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.


(* Prove the full adder does arithmetic *)
Lemma fullAdderFC_nat :
  forall (a b c : bool),
    let (l, h) := combinational (fullAdderFC a b c) in p_bits_to_nat [l; h] = p_bit_to_nat a + p_bit_to_nat b + p_bit_to_nat c.
Proof.
  intros.
  case a, b, c.
  all: reflexivity.
Qed.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

(*
    [ b3 ; b2 ; b1 ] ==  000 b3 b2 b1
 
Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | [] =>  0
  | b::bs => (shiftl (Nat.b2n b) (length bs)) + (bits_to_nat bs) 
  end.



Lemma fullAdderNat_correct : forall (cin : nat) (a : nat) (b : nat), cin < 2 -> a < 2 -> b < 2 ->
                             let (sum, carry) := combinational (fullAdderFC (testbit 0 cin, (testbit 0 a, testbit 0 b))) in
                             l := cin + a + b
                              
Proof.
  intros.   
  rewrite fullAdderFC_behaviour.
  simpl.
  unfold double.
  unfold Nat.b2n.

  rewrite 
  unfold combinational.
  unfold combinational.
  unfold fst.
  unfold nat2bool in *.
  simpl.
  unfold Nat.b2n.
  unfold double.

  all : simpl.
  auto.


Definition bool2nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Definition fullAdderNat (a : nat) (b : nat) (cin : nat)
  := cin + a + b.


Definition natPairToBool (sc : nat) (p : sc < 4) : bool * bool :=
  match p with
  | (S (S (S (S n)))) => fun _ => match False with end
  | s => fun _ => match s with
                  | 0 => (false, false)
                  | 1 => (true, false)
                  | 2 => (false, true)
                  | 3 => (true, true)
                  end
  end.

Lemma fullAdderNat_behaviour : forall (a : nat) (b : nat) (cin : nat),
                               a < 2 -> b < 2 -> cin < 2 ->
                               combinational (fullAdderFC (nat2bool cin, (nat2bool a, nat2bool b)))
                               = fullAdderNat a b cin.
Proof.
  intros.
  unfold fullAdderNat.
  unfold fullAdderFC.
  unfold combinational.
  simpl.
  unfold boolPairToNat.
  simpl.
  unfold bool2nat.
  unfold nat2bool.

Qed.
*)
