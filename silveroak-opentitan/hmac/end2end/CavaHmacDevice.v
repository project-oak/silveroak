Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.ZnWords.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.
Require Import HmacHardware.Hmac.
Require Import HmacSoftware.Constants.
Require Import HmacSoftware.HmacSemantics.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.TLUL.
Require Import Cava.Types.
Require Import Cava.Util.BitArithmetic.


Section WithParameters.
  Instance var : tvar := denote_type.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  (* TODO [for milestone 1: getting a simulation to run inside Coq using vm_compute]
     Fill in these parameters with values from the Cava Hmac device *)
  Global Instance hmac_device: device := {|
    device.state := denote_type (state_of hmac_top);
    device.is_ready_state s := True; (* FIXME *)
    device.run1 s i := Semantics.step hmac_top s (i, tt);
    device.addr_range_start := TOP_EARLGREY_HMAC_BASE_ADDR;
    device.addr_range_pastend := TOP_EARLGREY_HMAC_BASE_ADDR +
                                 HMAC_MSG_FIFO_REG_OFFSET +
                                 HMAC_MSG_FIFO_SIZE_BYTES;
    device.maxRespDelay := 1; (* FIXME *)
  |}.
  Global Instance hmac_timing: timing := {
    max_negative_done_polls := 16;
  }.

  (* TODO [for milestone 2: end-to-end proof]:
     Fill in these proofs to show that Cava Hmac device satisfies state machine *)
  Global Instance cava_hmac_satisfies_state_machine:
    device_implements_state_machine hmac_device hmac_state_machine.
  Proof.
    eapply Build_device_implements_state_machine.
  Admitted.

End WithParameters.
