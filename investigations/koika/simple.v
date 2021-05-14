Require Import Koika.Frontend.
Require Import Koika.Std.

Module Simple.
  Inductive reg_t := foo | bar.

  Definition R r :=
    match r with
    | foo => bits_t 32
    | bar => bits_t 4
    end.

  Definition r idx : R idx :=
    match idx with
    | foo => Bits.zero
    | bar => Bits.zero
    end.

  Inductive ext_fn_t := f1.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | f1 => {$ bits_t 1 ~> bits_t 32 $}
    end.

  Inductive rule_name_t := simple .

  Definition _simple : uaction reg_t ext_fn_t :=
    {{ if |4`d1| == |4`d0| then pass
       else (
        let y := extcall f1 (read0(foo)) in
        write0(foo, y)
        )
    }}.

  Definition simple_device : scheduler :=
    simple |> done.

  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | simple => _simple
                    end).

  Definition cr := ContextEnv.(create) r.

  Definition test_sigma1 (fn: ext_fn_t) : Sig_denote (Sigma fn) :=
    match fn with
    | f1 => fun _ => Bits.of_nat 32 1
    | do_zero_i => fun _ => Bits.zero
    | total_o => fun _ => Bits.zero
    end.
  Definition test_sigma2 (fn: ext_fn_t) : Sig_denote (Sigma fn) :=
    match fn with
    | f1 => fun _ => Bits.of_nat 32 1
    | do_zero_i => fun _ => Bits.of_nat 1 1
    | total_o => fun _ => Bits.zero
    end.

  Definition ext_fn_specs (fn: ext_fn_t) :=
    match fn with
    | f1 => {| efr_name := "f1"; efr_internal := true |}
    | do_zero_i => {| efr_name := "f2"; efr_internal := true |}
    | total_o => {| efr_name := "f3"; efr_internal :=  true |}
    end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := simple_device;
                     koika_module_name := "simple_device" |};

       ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
End Simple.

Definition prog := Interop.Backends.register Simple.package.
Extraction "simple.ml" prog.

