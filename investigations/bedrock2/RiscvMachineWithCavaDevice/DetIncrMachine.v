Require Import Cava.Cava.
Import Circuit.Notations.
Require Import Cava.CavaProperties.


Section WithCava.
  Context {signal} {semantics : Cava signal}.

  (* TODO doesn't Cava already provide these? *)
  Definition ite{T: SignalType}(cond: signal Bit)(thn els: signal T):
    cava (signal T) :=
    branches <- packV (Vector.of_list [els; thn]);;
    ctrl <- packV (Vector.of_list [cond]);;
    indexAt branches ctrl.

  Definition and3: signal Bit * signal Bit * signal Bit -> cava (signal Bit) :=
    fun '(x1, x2, x3) => x12 <- and2 (x1, x2);; and2 (x12, x3).

  Definition or3: signal Bit * signal Bit * signal Bit -> cava (signal Bit) :=
    fun '(x1, x2, x3) => x12 <- or2 (x1, x2);; or2 (x12, x3).

  Definition incr_update:
    (* input: *)
    signal Bit *             (* is_read_req *)
    signal Bit *             (* is_write_req *)
    signal (Vec Bit 32) *    (* req_addr (only relevant if is_reaq_req or is_write_req) *)
    signal (Vec Bit 32) *    (* req_value (only relevant if is_write_req *)
    (* state: *)
    signal Bit *             (* idle *)
    signal Bit *             (* busy *)
    signal Bit *             (* done *)
    signal (Vec Bit 32)      (* value *)
    -> cava (
    (* output: *)
    signal Bit *             (* is_resp *)
    signal (Vec Bit 32) *    (* resp (only relevant if is_resp *)
    (* state: *)
    signal Bit *             (* idle *)
    signal Bit *             (* busy *)
    signal Bit *             (* done *)
    signal (Vec Bit 32))     (* value *)
  := fun '(is_read_req, is_write_req, req_addr, req_value, idle, busy, done, value) =>
       initialized <- or3 (idle, busy, done);;
       idle <- ite initialized idle (constant true);;
       is_resp <- or2 (is_read_req, is_write_req);;
       (* bit #2 of the address determines if STATUS or VALUE register *)
       req_addr1 <- Vec.tl req_addr;;
       req_addr2 <- Vec.tl req_addr1;;
       is_status_req <- Vec.hd req_addr2;;
       is_value_req <- inv is_status_req;;
       is_value_write_req <- and2 (is_value_req, is_write_req);;
       no_pending_inp <- inv is_resp;;
       idle' <- and2 (idle, no_pending_inp);;
       busy' <- is_value_write_req;;
       done' <- or2 (busy, done);;
       value_plus_one <- incrN value;;
       value_or_input <- ite is_value_write_req req_value value;;
       value' <- ite busy value_plus_one value_or_input;;
       zeros <- Vec.const (constant false) 29;;
       v1 <- Vec.cons done zeros;;
       v2 <- Vec.cons busy v1;;
       v3 <- Vec.cons idle v2;;
       resp <- ite is_status_req v3 value;;
       ret (is_resp, resp, idle', busy', done', value').

  Definition incr: Circuit (signal Bit * signal Bit * signal (Vec Bit 32) * signal (Vec Bit 32))
                           (signal Bit * signal (Vec Bit 32)) :=
    Loop (Loop (Loop (Loop (Comb incr_update)))).

End WithCava.

Definition incr_device_step:
  (* input: current state, is_read_req, is_write_req, req_addr, req_value *)
  circuit_state incr -> bool * bool * Bvector 32 * Bvector 32 ->
  (* output: next state, is_resp, resp *)
  circuit_state incr * (bool * Bvector 32)
  := step incr.

Require Import coqutil.Datatypes.List.

(* like `simulate`, but also output the internal state, for more insightful debugging *)
Fixpoint simulate_with_state_rec{i o}(c: Circuit i o)(initial: circuit_state c)(inps: list i)
  : list (circuit_state c * o) :=
  match inps with
  | [] => []
  | inp :: rest => let r := step c initial inp in r :: simulate_with_state_rec c (fst r) rest
  end.
Definition simulate_with_state{i o}(c: Circuit i o): list i -> list (circuit_state c * o) :=
  simulate_with_state_rec c (reset_state c).

Example sample_trace := Eval compute in simulate_with_state incr [
  (false, false, N2Bv_sized 32 111, N2Bv_sized 32 111); (* no action *)
  (false, true, N2Bv_sized 32 0, N2Bv_sized 32 15);     (* write VALUE:=15 *)
  (true, false, N2Bv_sized 32 4, N2Bv_sized 32 111);    (* read STATUS *)
  (true, false, N2Bv_sized 32 4, N2Bv_sized 32 111);    (* read STATUS *)
  (true, false, N2Bv_sized 32 0, N2Bv_sized 32 111)     (* read VALUE *)
].

(* Print sample_trace. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Section WithParameters.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Global Instance counter_device: device := {|
    device.state := circuit_state incr;
    device.reset_state := reset_state incr;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay := 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device state_machine_parameters.
  Admitted.

End WithParameters.
