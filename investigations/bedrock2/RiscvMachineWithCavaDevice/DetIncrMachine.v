Require Import Cava.Cava.
Import Circuit.Notations.
Require Import Cava.CavaProperties.


Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition ite{T: SignalType}(cond: signal Bit)(thn els: signal T):
    cava (signal T) :=
    branches <- packV (Vector.of_list [thn; els]);;
    ctrl <- packV (Vector.of_list [cond]);;
    indexAt branches ctrl.

  (* no input/output, everything is state *)
  Definition incr_update: unit * (signal (Vec Bit 32)) ->
                    cava (unit * (signal (Vec Bit 32))) :=
    fun '(_, state) =>
      done <- Vec.hd state;;
      value <- Vec.tl state;;
      done' <- ret (constant true);;
      value_plus_one <- incrN value;;
      value' <- ite done value value_plus_one;;
      state' <- Vec.cons done' value';;
      ret (tt, state').

  Definition incr: Circuit unit unit := Loop (Comb incr_update).

End WithCava.

Definition device_state := Vector.t bool 32.

Eval simpl in circuit_state incr.

Definition incr_device_step(state: device_state): device_state :=
  snd (snd (fst (step incr (tt, (tt, state)) tt))).

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraMMIORiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.

Section WithParameters.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition INCR_DEVICE_ADDR: word := word.of_Z 0x10000.

  Definition bv_to_word(v: Vector.t bool 32): word :=
    word.of_Z (Z.of_N (Bv2N v)).

  Definition word_to_bv(w: word): Vector.t bool 32 :=
    N2Bv_sized 32 (Z.to_N (word.unsigned w)).

  Global Instance counter_device: device := {|
    device.state := device_state;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_DEVICE_ADDR;
    device.addr_range_pastend := word.add INCR_DEVICE_ADDR (word.of_Z 4);
    device.readReq(num_bytes: nat)(addr: word)(s: device_state) := s;
    device.readResp(s: device_state) := Some (bv_to_word s);
    device.writeReq(num_bytes: nat)(addr value: word)(s: device_state) := word_to_bv value;
    device.writeResp(s: device_state) := Some tt;
    device.maxRespDelay := 0;
  |}.

End WithParameters.
