Require Import Cava.Cava.
Import Circuit.Notations.
Require Import Cava.CavaProperties.


Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition ite{T: SignalType}(cond: signal Bit)(thn els: signal T):
    cava (signal T) :=
    branches <- packV (Vector.of_list [els; thn]);;
    ctrl <- packV (Vector.of_list [cond]);;
    indexAt branches ctrl.

  (* we need to add the Void because * is left-associative *)
  Definition void_and_state: Type :=
    (signal Void * signal Bit * signal Bit * signal Bit * signal Bit * signal Bit *
     signal (Vec Bit 32) * signal (Vec Bit 32) * signal Bit).

  (* no input/output, everything is state *)
  Definition incr_update: void_and_state -> cava (void_and_state) :=
    fun '(dummy_tt, pending_inp, outp_switch, idle, busy, done, value, output, output_en) =>
      pending_inp' <- constant false;;
      no_pending_inp <- inv pending_inp;;
      idle' <- and2 (idle, no_pending_inp);;
      busy' <- pending_inp;;
      done' <- or2 (busy, done);;
      value_plus_one <- incrN value;;
      value' <- ite busy value_plus_one value;;
      zeros <- Vec.const (constant false) 29;;
      v1 <- Vec.cons done zeros;;
      v2 <- Vec.cons busy v1;;
      v3 <- Vec.cons idle v2;;
      output_en' <- constant true;;
      output' <- ite outp_switch value v3;;
      ret (dummy_tt, pending_inp', outp_switch, idle', busy', done', value', output', output_en').

  Definition incr: Circuit (signal Void) (signal Void) :=
    Loop (Loop (Loop (Loop (Loop (Loop (Loop (Loop (Comb incr_update)))))))).

End WithCava.

Definition device_state: Type := Eval simpl in circuit_state incr.

Definition get_output: device_state -> Vector.t bool 32 :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) => output.

Definition get_output_en: device_state -> bool :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) => output_en.

Definition get_pending_inp: device_state -> bool :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) => pending_inp.

Definition set_outp_switch(b: bool): device_state -> device_state :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) =>
    (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, output_en), output),
                                   value), done), busy), idle), b), pending_inp)).

Definition set_outp_en(b: bool): device_state -> device_state :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) =>
    (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, b), output),
                                   value), done), busy), idle), outp_switch), pending_inp)).

Definition set_pending_inp(b: bool): device_state -> device_state :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) =>
    (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, output_en), output),
                                   value), done), busy), idle), outp_switch), b)).

Definition set_value(v: Vector.t bool 32): device_state -> device_state :=
  fun '(_, (_, (_, (_, (_, (_, (_, (_, (_, output_en), output),
                                value), done), busy), idle), outp_switch), pending_inp)) =>
    (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, output_en), output),
                                   v), done), busy), idle), outp_switch), pending_inp)).

Definition incr_device_step(state: device_state): device_state :=
  fst (step incr state tt).

Require Import coqutil.Datatypes.List.

Example sample_trace := Eval compute in
  let done := false in
  let busy := false in
  let idle := true in
  let outp_switch := false in
  let pending_inp := true in
  let output := Vector.const false 32 in
  let output_en := false in
  let value := (Vector.const true 2 ++ Vector.const false 30)%vector in
  let start := (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt,
      output_en), output), value), done), busy), idle), outp_switch), pending_inp)) in
  List.unfoldn incr_device_step 5 start.

(* Print sample_trace. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.

Section WithParameters.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition bv_to_word(v: Vector.t bool 32): word :=
    word.of_Z (Z.of_N (Bv2N v)).

  Definition word_to_bv(w: word): Vector.t bool 32 :=
    N2Bv_sized 32 (Z.to_N (word.unsigned w)).

  Global Instance counter_device: device := {|
    device.state := device_state;

    device.reset_state :=
      (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, (tt, false),
                                          word_to_bv (word.of_Z 0)), word_to_bv (word.of_Z 0)),
                                false), false), true), false), false));

    device.run1 := incr_device_step;

    device.addr_range_start := word.of_Z INCR_BASE_ADDR;
    device.addr_range_pastend := word.of_Z INCR_END_ADDR;

    device.readReq(num_bytes: nat)(addr: word)(s: device_state) :=
      (* TODO the address-to-register mapping could/should also be implemented in Cava *)
      set_outp_en false (set_outp_switch (word.eqb (word.of_Z 0) (word.and addr (word.of_Z 4))) s);
      (* outp_en will be set to true as soon as one cycle is run, which can set output
         according to outp_switch *)

    device.readResp(s: device_state) :=
      if get_output_en s then Some (bv_to_word (get_output s)) else None;

    device.writeReq(num_bytes: nat)(addr value: word)(s: device_state) :=
      set_value (word_to_bv value) (set_pending_inp true s);

    device.writeResp(s: device_state) :=
      if get_pending_inp s then None else Some tt;

    device.maxRespDelay := 1;
  |}.

End WithParameters.
