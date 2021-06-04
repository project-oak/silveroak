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
  Definition incr_update_v0: unit * (signal Bit * signal (Vec Bit 32)) ->
                    cava (unit * (signal Bit * signal (Vec Bit 32))) :=
    fun '(_, (busy, value)) =>
            busy' <- ret (constant false);;
            value' <- incrN value;;
            ret (tt, (busy', value')).

  (* Search (?signal (?A * ?B)%type) (?signal ?A * ?signal ?B)%type. *)
  Fail Definition incr: Circuit unit unit := Loop (Comb incr_update_v0).
  (* How to go from `signal A B` to `(signal A * signal B)`? *)

  (* no input/output, everything is state *)
  Definition incr_update: unit * (signal (Vec Bit 32)) ->
                    cava (unit * (signal (Vec Bit 32))) :=
    fun '(_, state) =>
      busy <- Vec.hd state;;
      value <- Vec.tl state;;
      busy' <- ret (constant false);;
      value_plus_one <- incrN value;;
      value' <- ite busy value_plus_one value;;
      state' <- Vec.cons busy' value';;
      ret (tt, state').

  Definition incr: Circuit unit unit := Loop (Comb incr_update).

End WithCava.

Definition device_state := Vector.t bool 32.

Check step incr.
Eval simpl in circuit_state incr.

Definition incr_device_step(state: device_state): device_state :=
  snd (snd (fst (step incr (tt, (tt, state)) tt))).

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraMMIORiscvMachine.

Definition TODO{T: Type}: T. Admitted.

Section Riscv.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition INCR_DEVICE_ADDR: word := word.of_Z 0x10000.

  Definition bv_to_word(v: Vector.t bool 32): word :=
    word.of_Z (Z.of_N (Bv2N v)).

  Definition word_to_bv(w: word): Vector.t bool 32 :=
    N2Bv_sized 32 (Z.to_N (word.unsigned w)).

  Instance mkWords: Words := {
    width := 32;
    width_cases := or_introl eq_refl;
    word := word;
    word_ok := word_ok;
  }.

  Instance mmioSpec: MMIOSpec device_state := {
    isExternalMMIOAddr a := False; (* no external MMIO at the moment *)

    isMMIOAligned n a := n = 4%nat /\ (word.unsigned a) mod 4 = 0;

    internalMMIORead a st post :=
      a = INCR_DEVICE_ADDR /\ post (bv_to_word st) st;

    internalMMIOWrite a v st post :=
      (* current state of device st is ignored and new state is set to v *)
      a = INCR_DEVICE_ADDR /\ post (word_to_bv v);

    extra_step st post := post (incr_device_step st);

    externalMMIOReadOK n t a v := True;
  }.

End Riscv.

Existing Instance mkWords.
Existing Instance mmioSpec.
