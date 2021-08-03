Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.ZnWords.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.Hmac.Constants.
Require Import Bedrock2Experiments.Hmac.HmacSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Section WithParameters.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  (* TODO [for milestone 1: getting a simulation to run inside Coq using vm_compute]
     Fill in these parameters with values from the Cava Hmac device *)
  Global Instance hmac_device: device := {|
    device.state := unit;
    device.is_ready_state := (eq tt);
    device.run1 s '(is_read_req, is_write_req, req_addr, req_value) :=
      let s' := s in
      let is_resp := true in
      let resp := req_value in
      (s', (is_resp, resp));
    device.addr_range_start := TOP_EARLGREY_HMAC_BASE_ADDR;
    device.addr_range_pastend := TOP_EARLGREY_HMAC_BASE_ADDR +
                                 HMAC_MSG_FIFO_REG_OFFSET +
                                 HMAC_MSG_FIFO_SIZE_BYTES;
    device.maxRespDelay := 1;
  |}.
  Global Instance hmac_timing: timing := {
    max_negative_done_polls := 16;
  }.

  (* TODO [for milestone 2: end-to-end proof]:
     Fill in these proofs to show that Cava Hmac device satisfies state machine *)
  Global Instance cava_hmac_satisfies_state_machine:
    device_implements_state_machine hmac_device state_machine_parameters.
  Proof.
    eapply Build_device_implements_state_machine.
  Admitted.

End WithParameters.
