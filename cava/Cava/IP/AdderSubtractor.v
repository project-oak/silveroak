(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Cava.Cava.
Import Circuit.Notations.

Section WithCava.
  Context {signal} {semantics:Cava signal}.

(* PIPELINE
                                  a
                                  ^
                                  |
         -----      -----       -----
        |     |    |     |     |     |
   b -->|Delay|--->|Delay|---->|  r  |----> c
        |     |    |     |     |     |
         -----      -----       -----
                                 ^
                                 |
                      +--- a ----+
                      ^
                      |
         -----      -----       -----
        |     |    |     |     |     |
   b -->|Delay|--->|  r  |---->|Delay|----> c
        |     |    |     |     |     |
         -----      -----       -----
                      ^
                      |
          +---- a ----+
          ^
          |
        -----       -----        -----
       |     |     |     |      |     |
   b ->|  r  |---->|Delay|----->|Delay|---> c
       |     |     |     |      |     |
        -----       -----        -----
          ^
          |
          a
 *)
(*
-  Pseudocode:
   pipeline 1 (r, a, (b:bs)) = r
   pipeline n (r, a, (b:bs)) = below (Delay >==> pipeline r a bs) (r >==> repeat (n-1) Delay)
-*)

  Definition below {A B C D E}
    (lower : Circuit (B * A) (C * A)) (upper : Circuit (D * A) (E * A))
    := First lower
       >==> Comb (fun '((c, a), d) => ret (c, (d,a))) >==>
       Second upper.

  Definition delayN {A} n
    := Vector.fold_left Compose (Comb (ret (t:=signal A))) (Vector.const Delay n).

  Fixpoint pipeline {A B C n} (r : Circuit (signal B * signal A) (signal C * signal A))
    : Circuit (signal (Vec B (S n)) * signal A) (signal (Vec C (S n)) * signal A)
    := match n with
       | 0 => First (Comb Vec.hd)
              >==> r >==>
              First (Comb (fun c => Vec.const c 1))
       | S n' =>
           Comb (fun '(bs,a) =>
             b <- Vec.hd bs ;;
             bs <- Vec.tl bs ;;
             ret ((b, a),bs))
           >==>
           below (r >==> First (delayN n) >==> Second Delay)
                 (First Delay >==> pipeline r)
           >==>
           Comb (fun '(c, (cs, a)) => cs <- Vec.cons c cs;; ret (cs, a))
       end.

  Definition c_addsub_0
    : Circuit (signal (Vec Bit 8) * signal (Vec Bit 8)) (signal (Vec Bit 9))
    := Comb (fun inp =>
         zipped <- Vec.map2
                     (fun '(a,b) => Vec.map_literal ret [a;b]%vector)
                     inp ;;
         ret (zipped, defaultSignal))
       >==>
       pipeline (Comb (fun '(xy,cin) =>
         x <- indexConst xy 0 ;;
         y <- indexConst xy 1 ;;
         fullAdder (cin, (x,y))))
       >==>
       Comb (fun '(vs,v) => Vec.shiftin v vs)
       .

  (*
  Eval cbv [pipeline below] in (fun A B C D (c : Circuit (signal (Vec B 2) * A) (signal (Vec C 2)* A)) => pipeline c (n:=1)).

    Definition c_addsub_0 (input : signal (Vec Bit 8) * signal (Vec Bit 8))
      : cava (signal (Vec Bit 9))
      := let '(x,y) := input in
      '(sum, carry) <- addC (x,y,zero) ;;
      Vec.shiftin carry sum.
    *)

End WithCava.
