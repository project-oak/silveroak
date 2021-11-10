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

           (busy', done', registers', tl_d2h') initially
           (false, (false, ([0; 1], default (t:=tl_d2h_t))))
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
(* Print sample_trace. *)

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

  Definition repr := (repr_state * list N * list tl_h2d * inner_repr)%type.

  Global Instance incr_invariant : invariant_for incr repr :=
    fun (state : denote_type (state_of incr)) repr =>
      let '((s_busy, (s_done, (s_regs, s_d2h))), (s_tlul, s_inner)) := state in
      let '(r_state, r_regs, r_tlul, r_inner) := repr in
      tlul_invariant (reg_count:=2) s_tlul r_tlul
      /\ inner_invariant s_inner r_inner
      /\ match r_state with
        | RSIdle => s_busy = false /\ s_done = false
                   /\ r_inner = IISIdle
                   /\ nth 1 r_regs 0%N = 1
        | RSBusy data => s_busy = true /\ s_done = false
                        /\ (exists c, r_inner = IISBusy data c)
                        /\ nth 1 r_regs 0%N = 2
        | RSDone res => s_busy = false /\ s_done = true
                       /\ (r_inner = IISDone res \/ r_inner = IISIdle)
                       /\ nth 0 r_regs 0%N = res
                       /\ nth 1 r_regs 0%N = 4
        end
      /\ s_regs = r_regs
      /\ length r_regs = 2%nat.

  Existing Instance tlul_specification.

  Instance incr_specification
    : specification_for incr repr :=
    {| reset_repr := (RSIdle, [0; 1], [], IISIdle);

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
      all: cbn; try (ssplit; try reflexivity;
                     destruct x0 as [|? [|]]; try discriminate H3; reflexivity).
      all: try (eapply outstanding_prec in H;
                try match goal with
                    | H: outstanding_h2d _ = Some _ |- outstanding_h2d _ = Some _ =>
                      apply H
                    end; destruct H; rewrite H in Htl_postc |- *; cbn in Htl_postc |- *;
                logical_simplify; subst; ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                try reflexivity;
                destruct x0 as [|? [|]]; try discriminate H3; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                   logical_simplify; tlsimpl;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; try cbn in Htl_postc; logical_simplify; subst; cbn; ssplit;
                try eexists;
                try reflexivity;
                destruct x0 as [|? [|]]; try discriminate H3; reflexivity).
      all: try (destruct a_valid; ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                try reflexivity;
                destruct x0 as [|? [|]]; try discriminate H3; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; logical_simplify;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; try cbn in Htl_postc; logical_simplify; subst;
                boolsimpl; destruct (negb (N.land a_address 4 =? 0)) eqn:Haddr;
                cbn; try (rewrite Haddr); ssplit;
                try (left; reflexivity);
                try (right; reflexivity);
                try reflexivity;
                destruct x0 as [|? [|]]; try discriminate H3; reflexivity).
      all: try (inversion H5; subst; clear H5;
            destruct x as [|[|[|?]]]; cbn; ssplit;
            try eexists;
            try (left; reflexivity);
            try (right; reflexivity);
            try reflexivity;
            try (destruct x0 as [|? [|]]; try discriminate H3; reflexivity);
            exfalso; lia).
      all: destruct H5; discriminate.
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
      all: try (destruct H5; discriminate).
      all: try (inversion H5; subst; clear H5;
            destruct x as [|[|[|?]]]; try reflexivity; exfalso; lia).
      all: try (eapply outstanding_prec in H;
                try match goal with
                    | H: outstanding_h2d _ = Some _ |- outstanding_h2d _ = Some _ =>
                      apply H
                    end; destruct H; rewrite H in Htl_postc |- *; cbn in Htl_postc |- *;
                logical_simplify; subst; cbn; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; logical_simplify;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; try cbn in Htl_postc; logical_simplify; subst; reflexivity).
      all: try (destruct a_valid; simplify_spec (tlul_adapter_reg (reg_count:=2));
                tlsimpl; logical_simplify;
                try match goal with
                    | H: true = true -> _ |- _ =>
                      destruct H; try reflexivity; subst
                    end; try cbn in Htl_postc; logical_simplify; subst;
                boolsimpl; destruct (negb (N.land a_address 4 =? 0)) eqn:Haddr;
                cbn; try (rewrite Haddr); reflexivity).
    - all: match goal with
           | |- length (match ?v with _ => _ end) = 2%nat => destruct v
           end;
        match goal with
        | |- context [update_repr ?ui ?ur] =>
          remember (update_repr (c:=inner) ui ur) as up eqn:?H;
            replace (update_repr (c:=inner) ui ur) with up;
            destruct up
        end;
        rewrite ! length_replace; assumption.
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
