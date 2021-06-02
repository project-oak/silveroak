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

Require Import Koika.Frontend.
Require Import AesCore.TileLink.

Definition key_t := bits_t 128.
Definition state_t := bits_t 128.
Definition keypair_t := bits_t 256.

Module CoSimulation.
  Inductive reg_t :=
    | registers (aes_regs: AesRegisterMap.reg_t)

    | core_state

    | iteration
    | key_pair
    | state
    | iv

    | is_decrypt
    | is_gen_dec_key
    | is_step
    | is_finishing
  .

  Definition R r :=
    match r with
    | registers regs => AesRegisterMap.R regs

    | core_state => bits_t 4

    | iteration => bits_t 4
    | key_pair => keypair_t
    | state => state_t
    | iv => bits_t 128

    | is_decrypt => bits_t 1
    | is_gen_dec_key => bits_t 1
    | is_step => bits_t 1
    | is_finishing => bits_t 1
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx return R idx with
    | registers regs => AesRegisterMap.r regs

    | core_state => Bits.zero

    | iteration => Bits.zero
    | key_pair => Bits.zero
    | state => Bits.zero
    | iv => Bits.zero

    | is_decrypt => Bits.zero
    | is_gen_dec_key => Bits.zero
    | is_step => Bits.zero
    | is_finishing => Bits.zero
    end.

  Inductive ext_fn_t := aes_cipher_step | aes_transpose | aes_key_expand | tl_io.

  Definition Sigma fn :=
    match fn with
    | aes_cipher_step => {$ state_t ~> state_t $}
    | aes_transpose => {$ state_t ~> state_t $}
    | aes_key_expand => {$ keypair_t ~> keypair_t $}

    | tl_io => {$ struct_t TLUL.tl_d2h_t ~> struct_t TLUL.tl_h2d_t $}
    end.

  Inductive rule_name_t :=
    | do_reg_interface

    | do_set_idle
    | do_trigger

    | do_encrypt_round
    | do_iter_counter
    | do_finish_op
    | do_key_expand
  .

  (* Pass TLUL interface packets to the TLUL decoding/register mapping routines *)
  Definition _do_reg_interface : uaction reg_t ext_fn_t :=
    {{
       let tl_o := registers.(AesRegisterMap.outgoing_tlul_packet)() in
       let tl_i := extcall tl_io (tl_o) in
       registers.(AesRegisterMap.incoming_tlul_packet)(tl_i)
    }}.

  (* Set status independently from '_do_iter_counter' so the value can rise at
    start. Alternatively we could initialize the value directly in the register map. *)
  Definition _do_set_idle : uaction reg_t ext_fn_t :=
    {{
       guard(!read0(is_step));

       registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_STATUS), |32`d1|)
    }}.

  (* When all registers have been written to trigger and copy control registers *)
  Definition _do_trigger : uaction reg_t ext_fn_t :=
    {{
       let status := registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_STATUS)) in

       (* Check we are idle *)
       guard(status == |32`d1|);

       (* Trigger start when first 16 registers have been written to at least
       * once *)
       let start := `
         Koika.SyntaxMacros.ortree (sz:=4) (fun bs =>
           {{ registers.(AesRegisterMap.is_write_dirty)( Ob~0 ++ #(bs) ) }}
         )` in

       guard(start);

       (* TODO(blaxill): should we clear only flags from the triggering
        * registers? *)
       registers.(AesRegisterMap.clear_all_flags)();

       (* |32`d1| = low status bit busy *)
       registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_STATUS), |32`d1|);

       let load_key_pair :=
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY0)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY1)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY2)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY3)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY4)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY5)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY6)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_KEY7))
       in

       let load_iv :=
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_IV0)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_IV1)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_IV2)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_IV3))
       in

       let load_data :=
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_DATA_IN0)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_DATA_IN1)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_DATA_IN2)) ++
         registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_DATA_IN3))
         in

       write0(key_pair, load_key_pair);
       write0(iv, load_iv);
       write0(state, load_data);

       let ctrl := registers.(AesRegisterMap.read)(#(AesRegisterMap.REG_AES_CTRL)) in

       if ctrl[|5`d0|] == Ob~0 then (
         (* encryption *)
         write0(is_step, Ob~1);
         write0(is_gen_dec_key, Ob~0);
         write0(is_decrypt, Ob~0)
       )
       else (
         (* decryption *)
         write0(is_step, Ob~1);
         write0(is_gen_dec_key, Ob~1);
         write0(is_decrypt, Ob~1)
       )
    }}.

  Definition _do_encrypt_round : uaction reg_t ext_fn_t :=
    {{
       guard(read0(is_step));
       guard(!read0(is_gen_dec_key));
       let iter := read0(iteration) in
       let st := read0(state) in
       let is_decrypt := read0(is_decrypt) in
       let is_first_round := iter == |4`d0| in
       let key := read0(key_pair) in

       (* TODO(blaxill): pass all variables: is_decrypt is_first_round num_rounds_regular k idx st ;; *)
       let st' := extcall aes_cipher_step (st) in

       write0(state, st')
    }}.

  Definition _do_iter_counter : uaction reg_t ext_fn_t :=
    {{
       guard(read0(is_step));
       let iter := read0(iteration) in
       let last_round := |4`d13| in
       let next_iter := iter + |4`d1| in

       if iter == last_round
       then (
         write0(iteration, |4`d0|);
         if read0(is_gen_dec_key)
         then write0(is_gen_dec_key, Ob~0)
         else write0(is_step, Ob~0))
       else
         write0(iteration, next_iter)
    }}.

  Definition _do_finish_op : uaction reg_t ext_fn_t :=
    {{
      guard(read0(iteration) == |4`d14| );
      guard(read0(is_step));
      guard(!read0(is_gen_dec_key));

      let data := read0(state) in
      let d0 := data[|7`d0|:+32] in
      let d1 := data[|7`d32|:+32] in
      let d2 := data[|7`d64|:+32] in
      let d3 := data[|7`d96|:+32] in

      registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_DATA_OUT0), d0);
      registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_DATA_OUT1), d1);
      registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_DATA_OUT2), d2);
      registers.(AesRegisterMap.write)(#(AesRegisterMap.REG_AES_DATA_OUT3), d3);

      write0(is_step, Ob~0);

      pass
    }}.

  Definition _do_key_expand : uaction reg_t ext_fn_t :=
    {{ guard(read0(is_step) || read0(is_gen_dec_key));
       let iter := read0(iteration) in
       let key_pair := read0(key_pair) in

       if iter == |4`d0| then
         (* swizzle *)
         (* TODO(blaxill): check correct *)
         let low := key_pair[|8`d0| :+ 128] in
         let high := key_pair[|8`d128| :+ 128] in
         write0(key_pair, low ++ high)
       else (
         let key_expand := extcall aes_key_expand (read0(key_pair)) in
         write0(key_pair, key_expand))
    }}.

  Definition aes_core : scheduler :=
       do_reg_interface
    |> do_set_idle
    |> do_trigger
    |> do_encrypt_round
    |> do_key_expand
    |> do_iter_counter
    |> do_finish_op
    |> done.

  Definition rules :=
    (* Eval vm_compute in *)
    tc_rules R Sigma
             (fun r => match r with
                       | do_reg_interface => _do_reg_interface
                       | do_set_idle => _do_set_idle
                       | do_trigger => _do_trigger
                       | do_iter_counter => _do_iter_counter
                       | do_encrypt_round => _do_encrypt_round
                       | do_finish_op => _do_finish_op
                       | do_key_expand => _do_key_expand
                    end).

  Definition external (_: rule_name_t) := false.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := fun _ => false;
                     koika_scheduler := aes_core;
                     koika_module_name := "aes_core" |};

       ip_sim := {| sp_ext_fn_specs _ := {| efs_name := "blackbox";
                                          efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs _ := {| efr_name := "blackbox";
                                              efr_internal := true |} |} |}.

  Definition circuits :=
    compile_scheduler rules external aes_core.

  Definition circuits_result sigma :=
    interp_circuits sigma circuits (lower_r (ContextEnv.(create) r)).

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition σ tlp_o fn : Sig_denote (Sigma fn) :=
    match fn with
    | aes_cipher_step => id
    | aes_transpose => id
    | aes_key_expand => id
    | tl_io => fun _ => tlp_o
    end.

  Require Koika.CompactSemantics.
  Opaque CompactSemantics.interp_cycle.

  Definition cycle tlp (r: ContextEnv.(env_t) R) :=
      CompactSemantics.interp_cycle (σ tlp) rules aes_core r.

  Lemma test :
    let env := (ContextEnv.(create) r) in
    cycle (value_of_bits Bits.zero) (cycle (value_of_bits Bits.zero) env) = env.
  Proof.
    intros r; unfold cycle.
    (* hangs: *)
    (* abstract_simpl.  (1* rewrite (interp_cycle_cps_correct_rev); simpl. *1) *)
  Abort.

End CoSimulation.

Definition prog := Interop.Backends.register CoSimulation.package.
