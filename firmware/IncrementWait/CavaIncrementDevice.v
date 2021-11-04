Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.TLUL.
Require Import Cava.Types.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.Tactics.

Import ListNotations.

Section Var.
  Import Expr.
  Import ExprNotations.
  Import PrimitiveNotations.

  Local Open Scope N.

  Context {var : tvar}.

  Definition incr_state := BitVec 2.
  Definition Idle       := Constant incr_state 0.
  Definition Busy1      := Constant incr_state 1.
  Definition Busy2      := Constant incr_state 2.
  Definition Done       := Constant incr_state 3.

  Definition inner
    : Circuit _ [Bit; BitVec 32] (Bit ** BitVec 32)
    := {{
      fun valid data =>
        let/delay '(istate; value) :=
           let istate' :=
               if istate == `Busy1` then `Busy2`
               else if istate == `Busy2` then `Done`
                    else if istate == `Done` then `Idle`
                         else (* istate == `Idle` *)
                           if valid then `Busy1`
                           else `Idle` in

           let value' :=
               if istate == `Busy2` then value + `K 1`
               else if istate == `Idle` then data
                    else value in

           (istate', value')
             initially default
           : denote_type (incr_state ** BitVec 32)
        in
        (istate == `Done`, value)
       }}.

  Definition incr
    : Circuit _ [tl_h2d_t] tl_d2h_t
    := {{
      fun tl_h2d =>
        (* Destruct and reassemble tl_h2d with a_address that matches the
           tlul_adapter_reg interface. *)
        let '(a_valid
              , a_opcode
              , a_param
              , a_size
              , a_source
              , a_address
              , a_mask
              , a_data
              , a_user
              ; d_ready) := tl_h2d in
        (* Bit #2 of the address determines which register is being accessed *)
        (*    (STATUS or VALUE). Zero out the other bits. *)
        let a_address := a_address & (`K 1` << 2) in
        let tl_h2d := (a_valid
                       , a_opcode
                       , a_param
                       , a_size
                       , a_source
                       , a_address
                       , a_mask
                       , a_data
                       , a_user
                       , d_ready) in

        let/delay '(busy, done, registers; tl_d2h) :=
           let '(tl_d2h'; req) := `tlul_adapter_reg` tl_h2d registers in
           let '(is_read, is_write, address, write_data; _write_mask) := req in

           let '(inner_res_valid; inner_res) := `inner` (!busy && !done && is_write) write_data in

           let busy' :=
               if busy then !inner_res_valid
               else !done && is_write in

           let done' :=
               if busy then inner_res_valid
               else if done then !(is_read && address == `K 0`)
                    else done in

           let registers' :=
               if inner_res_valid then `replace` registers `K (sz:=1) 0` inner_res
               else registers in

           let registers' :=
               if busy' then `replace` registers' `K (sz:=1) 1` `K 2`
               else if done' then `replace` registers' `K (sz:=1) 1` `K 4`
                    else `replace` registers' `K (sz:=1) 1` `K 1` in

           (busy', done', registers', tl_d2h') initially default
           : denote_type (Bit ** Bit ** Vec (BitVec 32) 2 ** tl_d2h_t)
        in

        tl_d2h
       }}.
End Var.

Definition sim {s i o} (c : Circuit s i o) (input : list (denote_type i))
  : list (denote_type s * denote_type i * denote_type o) :=
  fst (List.fold_left (fun '(acc, s) i =>
                         let '(s', o) := step c s i in
                         (acc ++ [(s, i, o)], s'))
                      input
                      ([], reset_state c)).

Example sample_trace :=
  Eval compute in
    let nop := set_d_ready true tl_h2d_default in
    let read_reg (r : N) :=
        set_a_valid true
        (set_a_opcode Get
        (set_a_size 2%N
        (set_a_address r
        (set_d_ready true tl_h2d_default)))) in
    let write_val (v : N) :=
        set_a_valid true
        (set_a_opcode PutFullData
        (set_a_size 2%N
        (set_a_address 0%N (* value-ref *)
        (set_a_data v
        (set_d_ready true tl_h2d_default))))) in

    sim incr
        [ (nop, tt)
          ; (read_reg 4, tt) (* status *)
          ; (nop, tt)
          ; (write_val 42, tt)
          ; (nop, tt)
          ; (nop, tt)
          ; (read_reg 4, tt) (* status *)
          ; (nop, tt)
          ; (read_reg 0, tt) (* value *)
          ; (nop, tt)
          ; (read_reg 4, tt) (* status *)
        ]%N.
(* Print sample_trace. *)

Section Spec.
  Local Open Scope N.

  Variant inner_state :=
  | IISIdle
  | IISBusy (data : N) (count : nat)
  | IISDone (res : N).

  Notation inner_repr := inner_state.

  Global Instance inner_invariant : invariant_for inner inner_repr :=
    fun (state : denote_type (state_of inner)) repr =>
      let '(istate, value) := state in
      match repr with
      | IISIdle => istate = 0
      | IISBusy data c => (0 < c <= 2)%nat /\ istate = N.of_nat c /\ value = data
      | IISDone res => istate = 3 /\ value = res
      end.

  Definition inner_spec_step (input : denote_type (input_of inner)) repr :=
    let '(valid, (data, tt)) := input in
    match repr with
    | IISIdle => if valid then IISBusy data 1 else IISIdle
    | IISBusy data 2 => IISDone ((data + 1) mod 2^32)
    | IISBusy data c => IISBusy data (c + 1)
    | IISDone _ => IISIdle
    end.

  Instance inner_specification
    : specification_for inner inner_repr :=
    {| reset_repr := IISIdle;

       update_repr :=
         fun (input : denote_type (input_of inner)) repr =>
           inner_spec_step input repr;

       precondition :=
         fun (input : denote_type (input_of inner)) repr => True;

       postcondition :=
         fun (input : denote_type (input_of inner)) repr
           (output : denote_type (output_of inner)) =>
           let repr' := inner_spec_step input repr in
           match repr' with
           | IISDone res => output = (true, res)
           | _ => exists res, output = (false, res)
           end;
    |}.

  Lemma inner_invariant_at_reset : invariant_at_reset inner.
  Proof.
    simplify_invariant inner. reflexivity.
  Qed.

  Lemma inner_invariant_preserved : invariant_preserved inner.
  Proof.
    intros (valid, (data, t)) state repr. destruct t.
    cbn in * |-. destruct state as (istate, value).
    intros repr' ? Hinvar Hprec; subst.
    simplify_invariant inner.
    simplify_spec inner.
    cbv [inner inner_spec_step]. stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).
    destruct repr as [|? iiscount|?]; logical_simplify; subst.
    - destruct valid; cbn; try ssplit; lia.
    - destruct iiscount as [|[|[|iiscount]]]; cbn; ssplit; lia.
    - reflexivity.
  Qed.

  Lemma inner_output_correct : output_correct inner.
  Proof.
    intros (valid, (data, t)) state repr. destruct t.
    cbn in * |-. destruct state as (istate, value).
    remember (update_repr (c:=inner) (valid, (data, tt)) repr) as repr'.
    intros Hinvar Hprec.
    simplify_invariant inner.
    simplify_spec inner.
    cbv [inner inner_spec_step]. stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).
    destruct repr as [|? iiscount|?]; logical_simplify; subst.
    - destruct valid; eexists; cbn; try ssplit; reflexivity.
    - destruct iiscount as [|[|[|iiscount]]]; try lia; try eexists; reflexivity.
    - eexists. reflexivity.
  Qed.

  Existing Instances inner_invariant_at_reset inner_invariant_preserved
           inner_output_correct.
  Global Instance inner_correctness : correctness_for inner.
  Proof. constructor; typeclasses eauto. Defined.


  Variant repr_state :=
  | RSIdle
  | RSBusy (data : N)
  | RSDone (res : N).

  Notation repr := (repr_state * list N * list tl_h2d * inner_repr)%type.

  Global Instance incr_invariant : invariant_for incr repr :=
    fun (state : denote_type (state_of incr)) repr =>
      let '((s_busy, (s_done, (s_regs, s_d2h))), (s_tlul, s_inner)) := state in
      let '(r_state, r_regs, r_tlul, r_inner) := repr in
      tlul_invariant (reg_count:=2) s_tlul r_tlul
      /\ inner_invariant s_inner r_inner
      /\ match r_state with
        | RSIdle => s_busy = false /\ s_done = false
                   /\ r_inner = IISIdle
        | RSBusy data => s_busy = true /\ s_done = false
                        /\ exists c, r_inner = IISBusy data c
        | RSDone res => s_busy = false /\ s_done = true
                       /\ (r_inner = IISDone res \/ r_inner = IISIdle)
        end
      /\ s_regs = r_regs.

  Existing Instance tlul_specification.

  Instance incr_specification
    : specification_for incr repr :=
    {| reset_repr := (RSIdle, [0; 0], [], IISIdle);

       update_repr :=
         fun (input : denote_type (input_of incr)) repr =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tlul, r_inner) := repr in

           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           let r_tlul' :=
               let tlul_input := (h2d, (r_regs, tt)) in
               update_repr (c:=tlul_adapter_reg (reg_count:=2))
                           tlul_input r_tlul in

           (* compute (some) tlul output *)
           let '(is_read, is_write, address, write_data) :=
               match outstanding_h2d (h2d :: r_tlul) with
               | None => (false, false, 0, 0)
               | Some h2d' =>
                 if a_opcode h2d' =? Get then
                   match outstanding_h2d r_tlul with
                   | None => (a_valid h2d, false, a_address h2d, 0)
                   | _ => (false, false, 0, 0)
                   end
                 else if a_opcode h2d' =? PutFullData then
                   match outstanding_h2d r_tlul with
                   | None => (false, a_valid h2d, a_address h2d, a_data h2d)
                   | _ => (false, false, 0, 0)
                   end
                 else (false, false, 0, 0)
               end in

           let r_inner' :=
               let inner_input := (match r_state with RSIdle => is_write | _ => false end, (write_data, tt)) in
               update_repr (c:=inner) inner_input r_inner in

           let r_state' :=
               match r_state with
               | RSDone _ =>
                 if negb (is_read && (address =? 0)) then r_state
                 else RSIdle
               | _ =>
                 match r_inner' with
                 | IISBusy data _ => RSBusy data
                 | IISDone res => RSDone res
                 | _ => r_state
                 end
               end in

           let r_regs' :=
               match r_inner' with
               | IISDone res => replace 0 res r_regs
               | _ => r_regs
               end in

           let r_regs' :=
               match r_state' with
               | RSIdle => replace 1 1 r_regs'
               | RSBusy _ => replace 1 2 r_regs'
               | RSDone _ => replace 1 4 r_regs'
               end in

           (r_state', r_regs', h2d :: r_tlul, r_inner');

       precondition :=
         fun (input : denote_type (input_of incr)) repr =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tlul, r_inner) := repr in

           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           let tlul_input := (h2d, (r_regs, tt)) in

           let prec_tlul :=
               precondition (tlul_adapter_reg (reg_count:=2))
                            tlul_input r_tlul in

           let prec_inner :=
               forall d2h is_read is_write address write_data write_mask,
                 postcondition (tlul_adapter_reg (reg_count:=2))
                               tlul_input r_tlul
                               (d2h, (is_read, (is_write, (address, (write_data, write_mask)))))
                 -> precondition inner (match r_state with RSIdle => is_write | _ => false end, (write_data, tt)) r_inner in

           prec_tlul /\ prec_inner;

       postcondition :=
         fun (input : denote_type (input_of incr)) repr
           (output : denote_type (output_of incr)) =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tlul, r_inner) := repr in

           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           let postc_tlul :=
               let tlul_input := (h2d, (r_regs, tt)) in
               exists req,
                 postcondition (tlul_adapter_reg (reg_count:=2))
                               tlul_input r_tlul
                               (output, req) in
           postc_tlul;
    |}.

  Lemma incr_invariant_at_reset : invariant_at_reset incr.
  Proof.
    simplify_invariant incr.
    cbn. ssplit; try reflexivity.
    apply (tlul_adapter_reg_invariant_at_reset (reg_count:=2)).
  Qed.

  Existing Instance tlul_adapter_reg_correctness.

  (* TODO: move these lemmas to TLUL.v *)
  Lemma outstanding_in_repr {reg_count : nat} : forall r_tlul t,
      outstanding_h2d r_tlul = Some t ->
      In t r_tlul.
  Proof.
    intros ? ?.
    induction r_tlul; intros Houts; cbn in Houts.
    - discriminate.
    - destruct (outstanding_h2d r_tlul) eqn:Houts'.
      + destruct d_ready.
        * discriminate.
        * apply in_cons. auto.
      + destruct (a_valid a).
        * inversion Houts. apply in_eq.
        * discriminate.
  Qed.

  Lemma outstanding_a_valid {reg_count : nat} : forall r_tlul t,
      outstanding_h2d r_tlul = Some t ->
      a_valid t = true.
  Proof.
    intros ? ?.
    induction r_tlul; intros Houts; cbn in Houts.
    - discriminate.
    - destruct (outstanding_h2d r_tlul) eqn:Houts'.
      + destruct d_ready.
        * discriminate.
        * auto.
      + destruct (a_valid a) eqn:Hvalid.
        * inversion Houts. subst. assumption.
        * discriminate.
  Qed.

  Lemma outstanding_prec {reg_count : nat} : forall tl_st r_tlul t,
      tlul_invariant (reg_count:=reg_count) tl_st r_tlul ->
      outstanding_h2d r_tlul = Some t ->
      a_opcode t = Get \/ a_opcode t = PutFullData.
  Proof.
    intros ? ? ? Hinvar Houts. simpl in *.
    apply (outstanding_in_repr (reg_count:=reg_count)) in Houts as Hin.
    unfold tlul_invariant in Hinvar. logical_simplify.
    eapply Forall_forall in H. 2: apply Hin.
    apply H.
    eapply (outstanding_a_valid (reg_count:=reg_count)).
    apply Houts.
  Qed.


  Lemma incr_invariant_preserved : invariant_preserved incr.
  Proof.
    intros (h2d, t) state (((r_state, r_regs), r_tlul), r_inner). destruct t.
    cbn in * |-. destruct state as ((busy, (done, (registers, d2h))), (tl_st, inner_st)).
    destruct_tl_h2d. destruct_tl_d2h.
    intros repr' ? Hinvar Hprec; subst.
    simplify_invariant incr. logical_simplify. subst.
    simplify_spec incr. logical_simplify. subst.
    (* destruct Hprec as [regs Hprec]. *)
    cbv [incr]. stepsimpl.
    use_correctness.
    match goal with
    | H: (match outstanding_h2d (_::r_tlul) with | _ => _ end) |- _ =>
      rename H into Htl_postc
    end.
    repeat (destruct_pair_let; cbn [fst snd]).
    ssplit.
    - eapply tlul_adapter_reg_invariant_preserved.
      2: apply H.
      + reflexivity.
      + assumption.
    - eapply inner_invariant_preserved.
      2: apply H0.
      + simpl in *.
        destruct r_inner; try reflexivity.
        destruct (outstanding_h2d r_tlul) eqn:Houts.
        * destruct d_ready; logical_simplify; subst.
          -- boolsimpl. destruct r_state; reflexivity.
          -- eapply outstanding_prec in H as Hprec_t. 2: apply Houts.
             destruct Hprec_t as [Hprec_t|Hprec_t];
               rewrite Hprec_t in *; cbn in Htl_postc |- *; logical_simplify; subst;
                 boolsimpl; destruct r_state; reflexivity.
        * destruct a_valid eqn:Hvalid; logical_simplify; subst.
          -- cbn in Htl_postc.
             match goal with
             | H: true = true -> _ |- _ =>
               destruct H; try reflexivity; subst
             end; cbn in Htl_postc; logical_simplify; subst;
               boolsimpl; destruct r_state; logical_simplify; subst;
                 reflexivity.
          -- boolsimpl; destruct r_state; reflexivity.
      + match goal with
        | H: context [_ -> precondition inner _ r_inner] |- _ =>
          eapply H
        end.
        do 8 eexists. ssplit.
        1-2: reflexivity.
        apply Htl_postc.
    - match goal with
      | H: context [_ -> precondition inner _ r_inner] |- _ => clear H
      end.
      destruct r_inner; destruct r_state; destruct inner_st;
        unfold inner_invariant in H0; logical_simplify; subst;
          try discriminate;
          try (destruct H4; discriminate).
      all: destruct (outstanding_h2d r_tlul) eqn:Houts;
        cbn [outstanding_h2d] in Htl_postc |- *; rewrite Houts in Htl_postc |- *.
      all: tlsimpl; destruct d_ready; logical_simplify; subst; boolsimpl.
      all: cbn; try (ssplit; reflexivity).
      all: try (eapply outstanding_prec in H;
                try match goal with
                    | H: outstanding_h2d _ = Some _ |- outstanding_h2d _ = Some _ =>
                      apply H
                    end; destruct H; rewrite H in Htl_postc |- *; cbn in Htl_postc |- *;
                logical_simplify; subst; ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; destruct H2;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; cbn in Htl_postc; logical_simplify; subst; cbn; ssplit;
                  try eexists; reflexivity).
      all: try (destruct a_valid; ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; destruct H2;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; cbn in Htl_postc; logical_simplify; subst;
                boolsimpl; destruct (negb (N.land a_address 4 =? 0)) eqn:Haddr;
                cbn; try (rewrite Haddr); ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                reflexivity).
      all: (inversion H4; subst; clear H4;
            destruct x as [|[|[|?]]]; cbn; ssplit;
            try eexists;
            try (left; reflexivity);
            try (right; reflexivity);
            try reflexivity;
            exfalso; lia).
    - match goal with
      | H: context [_ -> precondition inner _ r_inner] |- _ => clear H
      end.
      destruct r_inner; destruct r_state; destruct inner_st;
        unfold inner_invariant in H0; logical_simplify; subst;
          try discriminate.
      all: destruct (outstanding_h2d r_tlul) eqn:Houts;
        cbn [outstanding_h2d] in Htl_postc |- *; rewrite Houts in Htl_postc |- *.
      all: tlsimpl; destruct d_ready; logical_simplify; subst; boolsimpl.
      all: try reflexivity.
      all: try (eapply outstanding_prec in H;
                try match goal with
                    | H: outstanding_h2d _ = Some _ |- outstanding_h2d _ = Some _ =>
                      apply H
                    end; destruct H; rewrite H in Htl_postc |- *; cbn in Htl_postc |- *;
                logical_simplify; subst; cbn; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; destruct H2;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; cbn in Htl_postc; logical_simplify; subst; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; destruct H2;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; cbn in Htl_postc; logical_simplify; subst;
                boolsimpl; destruct (negb (N.land a_address 4 =? 0)) eqn:Haddr;
                cbn; try (rewrite Haddr); reflexivity).
      all: try (inversion H4; subst; clear H4;
            destruct x as [|[|[|?]]]; try reflexivity; exfalso; lia).
      all: try (destruct H4; discriminate).
  Qed.

  Lemma incr_output_correct : output_correct incr.
  Proof.
    intros (h2d, t) state (((r_state, r_regs), r_tlul), r_inner). destruct t.
    cbn in * |-. destruct state as ((busy, (done, (registers, d2h))), (tl_st, inner_st)).
    destruct_tl_h2d. destruct_tl_d2h.
    intros Hinvar Hprec; subst.
    simplify_invariant incr. logical_simplify. subst.
    simplify_spec incr. logical_simplify. subst.
    cbv [incr]. stepsimpl.
    use_correctness.
    match goal with
    | H: (match outstanding_h2d (_::r_tlul) with | _ => _ end) |- _ =>
      rename H into Htl_postc
    end.
    repeat (destruct_pair_let; cbn [fst snd]).
    tlsimpl.
    destruct r_inner; destruct r_state; destruct inner_st;
      unfold inner_invariant in H0; logical_simplify; subst;
        try discriminate;
        try (destruct H5; discriminate).
    all: destruct (outstanding_h2d r_tlul) eqn:Houts;
      cbn [outstanding_h2d] in Htl_postc |- *; rewrite Houts in Htl_postc |- *.
    all: tlsimpl; destruct d_ready; logical_simplify; subst; boolsimpl.
    all: do 9 eexists.
    all: ssplit; try reflexivity; tlsimpl; ssplit; try reflexivity; try assumption.
    all: try (eapply outstanding_prec in H;
              try match goal with
                  | H: outstanding_h2d _ = Some _ |- outstanding_h2d _ = Some _ =>
                    apply H
                  end; destruct H; rewrite H in Htl_postc |- *; cbn in Htl_postc |- *;
              logical_simplify; subst; ssplit;
              try (left; reflexivity);
              try (right; reflexivity);
              try assumption;
              reflexivity).
    all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
              tlsimpl; destruct H2;
              try match goal with
                  | H: true = true -> _ |- _ =>
                    destruct H; try reflexivity; subst
                  end; cbn in Htl_postc; logical_simplify; subst; cbn; ssplit;
              try eexists; try assumption; reflexivity).
    Unshelve. all: auto.
  Qed.

  Existing Instances incr_invariant_at_reset incr_invariant_preserved
           incr_output_correct.
  Global Instance incr_correctness : correctness_for incr.
  Proof. constructor; typeclasses eauto. Defined.
End Spec.

Require Import Coq.micromega.Lia.

Require Import riscv.Utility.Utility.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.fwd.

Require Import bedrock2.ZnWords.

Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Require Import Cava.Util.Tactics.

Section WithParameters.
  Instance var : tvar := denote_type.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition consistent_states
             '((reqid, (reqsz, (rspop, (error, (outstanding, (_we_o, _re_o))))))
               : denote_type (state_of (tlul_adapter_reg (reg_count := 2))))
             '((d_valid, (d_opcode, (d_param, (d_size, (d_source, (d_sink, (d_data, (d_user, (d_error, a_ready)))))))))
               : denote_type tl_d2h_t)
    : Prop :=
      d_valid = outstanding /\
      d_opcode = rspop /\
      (* d_param = 0 /\ *)
      d_size = reqsz /\
      d_source = reqid /\
      (* d_sink = 0 /\ *)
      (* d_data = ?? *)
      (* d_user = 0 /\ *)
      d_error = error /\
      a_ready = negb outstanding.

  Definition mk_counter_state (istate : N) (val : N) tl_d2h tlul_state
    : denote_type (state_of incr) :=
    ((istate, (val, tl_d2h)), tlul_state).

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);
    device.is_ready_state s := exists val tl_d2h tlul_state,
        consistent_states tlul_state tl_d2h
        /\ s = mk_counter_state 0 val tl_d2h tlul_state;
    device.run1 s i := Semantics.step incr s (i, tt);
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay '((istate, (val, tl_d2h)), tlul_state) h2d :=
      (* if the value register was requested, and we're in state Busy1, it will take one
         more cycle to respond, else we will respond immediately *)
      if ((a_address h2d mod 8 =? 0(*register address=VALUE*))%N && (istate =? 1 (*Busy1*))%N)%bool
      then 1%nat else 0%nat;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Inductive counter_related: IncrementWaitSemantics.state -> denote_type (state_of incr) -> Prop :=
  | IDLE_related: forall val tl_d2h tlul_state,
      consistent_states tlul_state tl_d2h ->
      counter_related IDLE (mk_counter_state 0 val tl_d2h tlul_state)
  | BUSY1_related: forall val tl_d2h tlul_state ncycles,
      (1 < ncycles)%nat ->
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles) (mk_counter_state 1 (word_to_N val) tl_d2h tlul_state)
  | BUSY2_related: forall val tl_d2h tlul_state ncycles,
      (0 < ncycles)%nat ->
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles) (mk_counter_state 2 (word_to_N val) tl_d2h tlul_state)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val tl_d2h tlul_state ncycles,
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles)
                      (mk_counter_state 3 (word_to_N (word.add (word.of_Z 1) val)) tl_d2h tlul_state)
  | DONE_related: forall val tl_d2h tlul_state,
      consistent_states tlul_state tl_d2h ->
      counter_related (DONE val) (mk_counter_state 3 (word_to_N val) tl_d2h tlul_state).

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; lia.

  Lemma incrN_word_to_bv: forall (x : word),
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall (x : Z),
      (0 <= x < 2 ^ 32)%Z -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Set Printing Depth 100000.

  Ltac destruct_pair_let_hyp :=
    match goal with
    | H: context [ match ?p with
                   | pair _ _ => _
                   end ] |- _ =>
      destruct p as [?p0 ?p1] eqn:?H0
    end.

  Ltac destruct_pair_equal_hyp :=
    match goal with
    | H: context [ (?l0, ?l1) = (?r0, ?r1) ] |- _ =>
      eapply pair_equal_spec in H; destruct H as [?H0 ?H1]
    end.

  Ltac destruct_tlul_adapter_reg_state :=
    match goal with
    | H : N * (N * (N * (bool * (bool * (bool * bool))))) |- _ =>
      destruct H as [?reqid [?reqsz [?rspop [?error [?outstanding [?we_o ?re_o]]]]]]
    end.

  Ltac destruct_consistent_states :=
    match goal with
    | H : consistent_states _ _ |- _ =>
      destruct H as (Hvalid & Hopcode & Hsize & Hsource & Herror & Hready)
    end.

  Lemma N_to_word_word_to_N: forall v, N_to_word (word_to_N v) = v.
  Proof. intros. unfold N_to_word, word_to_N. ZnWords. Qed.

(* TODO move to coqutil *)
Ltac contradictory H :=
  lazymatch type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  | False => case H
  end.
Require Import coqutil.Tactics.autoforward.
Ltac fwd_step ::=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]
  | H: ?x = ?x |- _ => clear H
  | H: True |- _ => clear H
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    (* we don't use `inversion H` or `injection H` because they unfold definitions *)
    inv_rec LHS RHS;
    clear H
  | E: ?x = ?RHS |- context[match ?x with _ => _ end] =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end], E: ?x = ?RHS |- _ =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end] |- _ =>
    (* note: recursive invocation of fwd_step for contradictory cases *)
    destr x; try solve [repeat fwd_step; contradictory H]; []
  | H: _ |- _ => autoforward with typeclass_instances in H
  | |- _ => progress subst
  | |- _ => progress fwd_rewrites
  end.

  Axiom TODO: False.

  (* Set Printing All. *)
  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related);
      intros.
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      simpl in *. subst. inversion H0. subst. eexists _, _, _. eauto.
    - (* initial_states_are_related: *)
      simpl in *. destruct H0 as (val & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* initial_state_exists: *)
      simpl in *. destruct H as (val & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      simpl in sL1, sL2.
      destruct_tl_h2d. simpl in H. subst.
      cbn in H1.
      repeat (destruct_pair_let_hyp;
              repeat (destruct_pair_equal_hyp; subst; cbn [fst snd])).
      inversion H0; subst;
        try (rewrite incrN_word_to_bv);
        try (constructor; try lia; simpl; boolsimpl; ssplit; reflexivity).
    - (* state_machine_read_to_device_read_or_later: *)
      case TODO.
      (*
      cbn [counter_device device.state device.is_ready_state device.run1 device.addr_range_start
           device.addr_range_pastend device.maxRespDelay] in *.
      cbn [increment_wait_state_machine
             state_machine.state
             state_machine.register
             state_machine.is_initial_state
             state_machine.read_step
             state_machine.write_step
             state_machine.reg_addr
             state_machine.isMMIOAddr] in *.
      simpl in sL. destruct sL as ((istate & value & tl_d2h) & tlul_state).
      destruct_tl_d2h. destruct_tlul_adapter_reg_state.
      destruct H as [v [sH' [Hbytes H]]]. rewrite Hbytes.
      tlsimpl.
      destruct r; simp.
      + (* r=VALUE *)
        destruct_tl_h2d.
        cbn in *. subst.

        destruct_consistent_states. subst.
        destruct outstanding; cbn in H1|-*; fwd.


          eexists _, _, _; ssplit; try reflexivity; cbn; rewrite Z_word_N by lia;
            try (eapply IDLE_related; unfold consistent_states; ssplit; reflexivity);
            try (apply N_to_word_word_to_N).
      + (* r=STATUS *)
        destruct sH; [| |].
        * (* sH=IDLE *)
          inversion H0. subst.
          destruct_consistent_states. subst. cbn.
          repeat (rewrite Z_word_N by lia; cbn).
          unfold status_value, STATUS_IDLE, N_to_word, word_to_N.
          destruct outstanding; eexists _, _, _; ssplit; try reflexivity;
              try (apply IDLE_related; simpl; ssplit; reflexivity);
              try (simpl; unfold N_to_word; ZnWords).
        * (* sH=BUSY *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, N_to_word, word_to_N, status_value, STATUS_BUSY.
          rewrite word.unsigned_of_Z. unfold word.wrap.
          inversion H0; subst; [| |].
          -- (* BUSY1_related *)
            destruct outstanding; eexists _, _, _; simpl; [|].
            ++ ssplit; try reflexivity; [|].
               ** rewrite incrN_word_to_bv.
                  apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
               ** right. eexists. ssplit; try reflexivity; [|].
                  --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                  --- simpl. ZnWords.
            ++ ssplit; try reflexivity; [|].
               ** apply BUSY2_related. 1: shelve. unfold consistent_states. ssplit; reflexivity.
               ** right. eexists. ssplit; try reflexivity; [|].
                  --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                  --- simpl. ZnWords.
                      Unshelve. lia.
          -- (* BUSY2_related *)
            destruct outstanding; eexists _, _, _; simpl; [|].
            ++ ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply DONE_related; unfold consistent_states; ssplit; reflexivity.
              ** left. simpl. ssplit; try reflexivity. ZnWords.
            ++ ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
              ** right. eexists. ssplit; try reflexivity; [|].
                 --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                 --- simpl. ZnWords.
          -- (* BUSY_done_related *)
            (* the transition that was used to show that sH is not stuck was *)
            (* a transition from BUSY to BUSY returning a busy flag, but *)
            (* since the device already is in done state, it will return a *)
            (* done flag in this transition, so the transition we use to *)
            (* simulate what happened in the device is a BUSY-to-DONE *)
            (* transition returning a done flag instead of a BUSY-to-BUSY *)
            (* transition returning a busy flag. *)
            destruct outstanding; eexists _, _, _; boolsimpl; simpl;
              ssplit; try reflexivity;
                try (apply DONE_related; unfold consistent_states; ssplit; reflexivity);
                try (left; split; try reflexivity; simpl; ZnWords).
        * (* sH=DONE *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, N_to_word, word_to_N, status_value, STATUS_BUSY.
          rewrite !word.unsigned_of_Z. unfold word.wrap.
          inversion H0. subst.
          destruct outstanding; eexists _, _, _; boolsimpl; simpl;
            ssplit; try reflexivity;
              try (eapply DONE_related; unfold consistent_states; ssplit; reflexivity);
              try (simpl; ZnWords).
      *)
    - (* state_machine_write_to_device_write_or_later: *)
      case TODO.
      (*
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. simpl in tl_d2h. simpl in tlul_state.
      destruct_tl_d2h. destruct_tlul_adapter_reg_state. subst. cbn.
      unfold word_to_N.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      destruct outstanding; boolsimpl; simpl;
        eexists _, _, _; ssplit; try reflexivity; try assumption; apply BUSY1_related;
          try lia;
          try (unfold consistent_states; ssplit; reflexivity).
      *)
    - (* read_step_unique: *)
      simpl in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      simpl in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      simpl in *. subst. reflexivity.
  Qed.
End WithParameters.
