
Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Import Circuit.Notations.

(*|
.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  (* TODO: fix mux currying *)
  Definition mux2 {A} (i : signal Bit * (signal A * signal A)) :=
    mux2 (fst i) (snd i).

(*|
Exponentiation by squaring!
|*)

  (* sliding window with table? *)

  (* exponentiation by squaring, no trailing 0s *)
  Definition exp_by_squaring_naive {A} (init : combType A)
             (square : Circuit (signal A) (signal A))
             (multiply : Circuit (signal A) (signal A))
    : Circuit (signal Bit) (signal A) :=
    LoopInit init
             ((* start: exp[i], r1, r2 *)
               Second (square >==> (* r^2 *)
                              Comb fork2 >==> (* r^2, r^2 *)
                              Second multiply (* r^2, r^2*x *))
                      >==> (* exp[i], (r^2, r^2*x) *)
                      Comb (mux2 >=> fork2) (* acc, acc *)).

  (* exponentiation by squaring *)
  Definition exp_by_squaring {A} (init : combType A)
             (square : Circuit (signal A) (signal A))
             (multiply : Circuit (signal A) (signal A))
    : Circuit (signal Bit) (signal A) :=
    LoopInit (i:=signal Bit) (o:=signal A) (s:=A) init
             ((* start: exp[i], r *)
               Second (square >==> (* r^2 *)
                              Comb fork2 >==> (* r^2, r^2 *)
                              Second multiply (* r^2, r^2*x *))
                      >==> (* exp[i], (r^2, r^2*x) *)
                      Comb (first fork2 >=> (* (exp[i], exp[i]), (r^2, r^2*x) *)
                                  pair_right >=> (* exp[i], (exp[i], (r^2, r^2*x)) *)
                                  second mux2 >=> (* exp[i], acc *)
                                  second fork2 >=> (* exp[i], (acc, acc) *)
                                  pair_left) >==> (* (exp[i], acc), acc *)
                      First (Loop (Comb (pair_right >=> (* exp[i], (acc, out) *)
                                                    second swap >=> (* exp[i], (out, acc) *)
                                                    mux2 >=> (* out' *)
                                                    fork2))) (* out', acc *)).

(*|
.. coq:: none
|*)

End WithCava.

(*|
TODO: netlist
|*)

(* Compute 3 * 9 = 27 using exponentiation by squaring to save operations (9 = 1001):
   let w := 0 + 0 + 3 in
   let x := w + w in
   let y := x + x in
   let z := y + y + x in
   z *)
Compute map Bv2N
        (let double := Comb (fork2 >=> addN) in
         let add := Comb (fun v => addN (N2Bv_sized 8 3, v)) in
         simulate (exp_by_squaring_naive (A:=Vec Bit 8) (N2Bv_sized 8 0) double add)
                  (Vector.to_list (N2Bv_sized 3 5))).

Compute map Bv2N
        (let double := Comb (fork2 >=> addN) in
         let add := Comb (fun v => addN (N2Bv_sized 8 3, v)) in
         simulate (exp_by_squaring_naive (A:=Vec Bit 8) (N2Bv_sized 8 0) double add)
                  (Vector.to_list (N2Bv_sized 8 5))).

Compute map Bv2N
        (let double := Comb (fork2 >=> addN) in
         let add := Comb (fun v => addN (N2Bv_sized 8 3, v)) in
         simulate (exp_by_squaring (A:=Vec Bit 8) (N2Bv_sized 8 0) double add)
                  (Vector.to_list (N2Bv_sized 8 5))).

Definition fake_mul {n} x : Circuit (combType (Vec Bit n)) (combType (Vec Bit n)) :=
  Comb (fun v => ret (N2Bv_sized n (Bv2N v * x))).
Definition fake_square {n} : Circuit (combType (Vec Bit n)) (combType (Vec Bit n)) :=
  Comb (fun v => ret (N2Bv_sized n (Bv2N v * Bv2N v))).

Compute circuit_state (exp_by_squaring (A:=Vec Bit 8)
                          (N2Bv_sized 8 1)
                          fake_square
                          (fake_mul 3)).
(* Compute 3 ^ 5 = 243 *)
Compute map Bv2N
        (simulate (exp_by_squaring (A:=Vec Bit 8)
                          (N2Bv_sized 8 1)
                          fake_square
                          (fake_mul 3))
                  (Vector.to_list (N2Bv_sized 8 5))).

(*|
TODO: proofs
|*)

(* proof of binexp in general *)
