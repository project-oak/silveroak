Section Cava1.
  Require Import Cava.Cava.
  Import Circuit.Notations.
  Require Import Cava.CavaProperties.

  Section WithCava.
    Context {signal} {semantics : Cava signal}.

    Program Definition test1_update:
      (* input: *)
      signal Bit *
      (* state: *)
      signal Bit
      -> cava (
            (* output: *)
            signal Bit *
            (* state: *)
            signal Bit)
      := fun '(input, st) =>
           st' <- localSignal input
           ;; ret (st, st').

    Definition test1: Circuit (signal Bit) (signal Bit) :=
      Loop (Comb test1_update).
  End WithCava.

  Example test1_trace :=
    Eval compute in simulate test1
                             [ false
                               ; true
                               ; false ].
  Print test1_trace.
  (* test1_trace = [false; false; true]
          : list bool *)
End Cava1.


Section Cava2.
  From Cava Require Import
       Expr
       Primitives
       Semantics
       Types.

  Import ExprNotations.
  Import PrimitiveNotations.

  Section Var.
    Import ExprNotations.
    Context {var : tvar}.

    Definition test2
      : Circuit _
                (* Input *)
                [ Bit ]
                (* Output *)
                Bit
      := {{
        fun input =>
          let/delay st :=
             let st' := input in
             st' initially false : denote_type Bit
          in
          st
         }}.
  End Var.

  Example test2_trace :=
    Eval compute in simulate test2
                             [ (false, tt)
                               ; (true, tt)
                               ; (false, tt) ].
  Print test2_trace.
  (* test2_trace = [false; true; false]%list
          : list bool *)
End Cava2.
