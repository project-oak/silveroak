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
           (false, (false, ([0; 1], set_a_ready true (default (t:=tl_d2h_t)))))
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

  Variant repr_state :=
  | ReprIdle
  | ReprBusy (data : N) (count : nat)
  | ReprDone (res : N).

  Notation inner_repr := repr_state.

  Global Instance inner_invariant : invariant_for inner inner_repr :=
    fun (state : denote_type (state_of inner)) repr =>
      let '(istate, value) := state in
      match repr with
      | ReprIdle => istate = 0
      | ReprBusy data c => (0 < c <= 2)%nat /\ istate = N.of_nat c /\ value = data
      | ReprDone res => istate = 3 /\ value = res
      end.

  Definition inner_spec_step (input : denote_type (input_of inner)) repr :=
    let '(valid, (data, tt)) := input in
    match repr with
    | ReprIdle => if valid then ReprBusy data 1 else ReprIdle
    | ReprBusy data 2 => ReprDone ((data + 1) mod 2^32)
    | ReprBusy data c => ReprBusy data (c + 1)
    | ReprDone _ => ReprIdle
    end.

  Instance inner_specification
    : specification_for inner inner_repr :=
    {| reset_repr := ReprIdle;

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
           | ReprDone res => output = (true, res)
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
    - destruct valid; cbn; ssplit; lia.
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
    - destruct valid; eexists; cbn; ssplit; reflexivity.
    - destruct iiscount as [|[|[|iiscount]]]; try lia; eexists; reflexivity.
    - eexists. reflexivity.
  Qed.

  Existing Instances inner_invariant_at_reset inner_invariant_preserved
           inner_output_correct.
  Global Instance inner_correctness : correctness_for inner.
  Proof. constructor; typeclasses eauto. Defined.

  Definition repr := (repr_state * list N * TLUL.repr_state * inner_repr)%type.

  Global Instance incr_invariant : invariant_for incr repr :=
    fun (state : denote_type (state_of incr)) repr =>
      let '((s_busy, (s_done, (s_regs, s_d2h))), (s_tlul, s_inner)) := state in
      let '(r_state, r_regs, r_tl, r_inner) := repr in
      tlul_invariant (reg_count:=2) s_tlul r_tl
      /\ match r_tl with
        | TLUL.Idle =>
          d_valid    s_d2h = false
          /\ d_error  s_d2h = false
          /\ a_ready  s_d2h = true
        | TLUL.OutstandingAccessAckData h2d regs =>
          d_valid    s_d2h = true
          /\ d_opcode s_d2h = AccessAckData
          /\ d_param  s_d2h = 0
          /\ d_size   s_d2h = (a_size h2d)
          /\ d_source s_d2h = (a_source h2d)
          /\ d_sink   s_d2h = 0
          /\ d_data   s_d2h = (List.nth (N.to_nat ((((a_address h2d) / 4) mod (2 ^ 30)))) regs 0%N)
          /\ d_user   s_d2h = 0
          /\ d_error  s_d2h = false
          /\ a_ready  s_d2h = false
        | TLUL.OutstandingAccessAck h2d  =>
          d_valid    s_d2h = true
          /\ d_opcode s_d2h = AccessAck
          /\ d_param  s_d2h = 0
          (* /\ d_size   s_d2h =  *)
          /\ d_source s_d2h = (a_source h2d)
          /\ d_sink   s_d2h = 0
          /\ d_user   s_d2h = 0
          /\ d_error  s_d2h = false
          /\ a_ready  s_d2h = false
        end
      /\ inner_invariant s_inner r_inner
      /\ match r_state with
        | ReprIdle => s_busy = false /\ s_done = false
                     /\ r_inner = ReprIdle
                     /\ nth 1 r_regs 0%N = 1
        | ReprBusy data count => s_busy = true /\ s_done = false
                                /\ r_inner = ReprBusy data count
                                /\ nth 1 r_regs 0%N = 2
        | ReprDone res => s_busy = false /\ s_done = true
                         /\ (r_inner = ReprDone res \/ r_inner = ReprIdle)
                         /\ nth 0 r_regs 0%N = res
                         /\ nth 1 r_regs 0%N = 4
        end
      /\ s_regs = r_regs
      /\ length r_regs = 2%nat.

  Existing Instance tl_specification.

  Instance incr_specification
    : specification_for incr repr :=
    {| reset_repr := (ReprIdle, [0; 1], TLUL.Idle, ReprIdle);

       update_repr :=
         fun (input : denote_type (input_of incr)) repr =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tl, r_inner) := repr in

           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           let r_tl' :=
               let tlul_input := (h2d, (r_regs, tt)) in
               update_repr (c:=tlul_adapter_reg (reg_count:=2))
                           tlul_input r_tl in

           (* compute (some) tlul output *)
           let '(is_read, is_write, address, write_data) :=
               match r_tl' with
               | TLUL.Idle => (false, false, 0, 0)
               | TLUL.OutstandingAccessAckData _ _ =>
                 match r_tl with
                   | TLUL.Idle => (a_valid h2d, false, a_address h2d, 0)
                   | _ => (false, false, 0, 0)
                 end
               | TLUL.OutstandingAccessAck _ =>
                 match r_tl with
                 | TLUL.Idle => (false, a_valid h2d, a_address h2d, a_data h2d)
                 | _ => (false, false, 0, 0)
                 end
               end in

           let r_inner' :=
               let inner_input := (match r_state with ReprIdle => is_write | _ => false end,
                                   (write_data, tt)) in
               update_repr (c:=inner) inner_input r_inner in

           let r_state' :=
               match r_state with
               | ReprDone _ =>
                   if (is_read && (address =? 0))%bool then ReprIdle
                   else r_state
               | _ =>
                 match r_inner' with
                 | ReprBusy data count => ReprBusy data count
                 | ReprDone res => ReprDone res
                 | _ => r_state
                 end
               end in

           let r_regs' :=
               match r_inner' with
               | ReprDone res => replace 0 res r_regs
               | _ => r_regs
               end in

           let r_regs' :=
               match r_state' with
               | ReprIdle => replace 1 1 r_regs'
               | ReprBusy _ _ => replace 1 2 r_regs'
               | ReprDone _ => replace 1 4 r_regs'
               end in

           (r_state', r_regs', r_tl', r_inner');

       precondition :=
         fun (input : denote_type (input_of incr)) repr =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tl, r_inner) := repr in

           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           let tlul_input := (h2d, (r_regs, tt)) in

           let prec_tlul :=
               precondition (tlul_adapter_reg (reg_count:=2))
                            tlul_input r_tl in

           let prec_inner :=
               forall d2h is_read is_write address write_data write_mask,
                 postcondition (tlul_adapter_reg (reg_count:=2))
                               tlul_input r_tl
                               (d2h, (is_read, (is_write, (address, (write_data, write_mask)))))
                 -> precondition inner (match r_state with ReprIdle => is_write | _ => false end,
                                       (write_data, tt)) r_inner in

           prec_tlul /\ prec_inner;

       postcondition :=
         fun (input : denote_type (input_of incr)) repr
           (output : denote_type (output_of incr)) =>
           let '(i_h2d, tt) := input in
           let '(r_state, r_regs, r_tl, r_inner) := repr in
           let h2d := set_a_address (N.land (a_address i_h2d) 4) i_h2d in

           (* let postc_tlul := *)
           (*     let tlul_input := (h2d, (r_regs, tt)) in *)
           (*     exists req, *)
           (*       postcondition (tlul_adapter_reg (reg_count:=2)) *)
           (*                     tlul_input r_tl *)
           (*                     (output, req) in *)
           (* postc_tlul; *)
           True;
    |}.

  Lemma incr_invariant_at_reset : invariant_at_reset incr.
  Proof.
    simplify_invariant incr.
    cbn. ssplit; [apply (tlul_adapter_reg_invariant_at_reset (reg_count:=2))
                 |reflexivity..].
  Qed.

  Existing Instance tlul_adapter_reg_correctness.

  Lemma incr_invariant_preserved : invariant_preserved incr.
  Proof.
    intros (h2d, t) state (((r_state, r_regs), r_tl), r_inner). destruct t.
    cbn in * |-. destruct state as ((busy, (done, (registers, d2h))), (tl_st, inner_st)).
    destruct_tl_h2d. destruct_tl_d2h.
    intros repr' ? Hinvar Hprec; subst.
    simplify_invariant incr. logical_simplify. subst.
    simplify_spec incr. logical_simplify. subst.
    (* destruct Hprec as [regs Hprec]. *)
    match goal with
    | |- context [step incr ?s ?i] =>
      remember (step incr s i) as step eqn:Estep;
        cbv -[Semantics.step inner tlul_adapter_reg] in Estep;
          subst
    end.
    stepsimpl.
    use_correctness.
    clear H5.
    rename H9 into Hpostc_tl.
    repeat (destruct_pair_let; cbn [fst snd]).
    ssplit.
    - eapply tlul_adapter_reg_invariant_preserved.
      2: apply H.
      + reflexivity.
      + assumption.
    - pose (r_tl_:=r_tl); destruct r_tl; logical_simplify; subst.
      + destruct_tl_h2d; destruct_tl_d2h; tlsimpl; subst.
        pose (r_state_:=r_state); destruct r_state; cbn in *; logical_simplify; subst;
          pose (a_valid_:=a_valid); (destruct a_valid;
                                     [ match goal with
                                       | H: true = true -> _ |- _ =>
                                         destruct H; [auto|subst..]
                                       end|]); cbn in *; logical_simplify; subst;
            ssplit; auto.
      + destruct_tl_h2d; destruct_tl_d2h; tlsimpl; subst.
        pose (r_state_:=r_state); destruct r_state; cbn in *; logical_simplify; subst;
          pose (d_ready_:=d_ready); destruct d_ready; cbn in *; logical_simplify; subst;
            ssplit; auto.
      + destruct_tl_h2d; destruct_tl_d2h; tlsimpl; subst.
        pose (r_state_:=r_state); destruct r_state; cbn in *; logical_simplify; subst;
          pose (d_ready_:=d_ready); destruct d_ready; cbn in *; logical_simplify; subst;
            ssplit; reflexivity.
    - eapply inner_invariant_preserved.
      2: eassumption.
      + simpl in *.
        destruct r_inner; try reflexivity.
        destruct r_tl eqn:Houts; logical_simplify; subst.
        * destruct a_valid eqn:Hvalid; logical_simplify; subst.
          -- match goal with
             | H: true = true -> _ |- _ =>
               destruct H; try reflexivity; subst
             end; logical_simplify; subst;
               boolsimpl; destruct r_state; logical_simplify; subst;
                 cbn in Hpostc_tl |- *; logical_simplify; subst; reflexivity.
          -- boolsimpl; destruct r_state; reflexivity.

        * destruct d_ready; logical_simplify; subst;
            boolsimpl; destruct r_state; reflexivity.
        * destruct d_ready; logical_simplify; subst;
            boolsimpl; destruct r_state; reflexivity.
      + simplify_spec inner. auto.
    - destruct r_tl; destruct r_inner; destruct r_state; destruct inner_st;
        logical_simplify; subst; simplify_invariant inner; try discriminate.
      all: simplify_spec (tlul_adapter_reg (reg_count:=2)); logical_simplify; tlsimpl; subst.
      all: destruct a_valid; [destruct H3; subst|]; cbn in Hpostc_tl; logical_simplify; subst; cbn.
      all: eauto.
      all: destruct_tl_d2h; tlsimpl; subst.
      all: try (destruct (N.land a_address 4 =? 0) eqn:Haddr;
               ssplit; eauto;
               destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
      all: try (destruct count as [|[|[|]]]; [lia|..|lia]; cbn;
             ssplit; eauto;
             destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
      all: try (destruct H6; discriminate).
      all: try (destruct d_ready; logical_simplify; subst; cbn;
                  ssplit; eauto;
                  destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
    - destruct r_tl; destruct r_inner; destruct r_state; destruct inner_st;
        logical_simplify; subst.
      all: simplify_invariant inner.
      all: try discriminate.
      all: simplify_spec (tlul_adapter_reg (reg_count:=2)); logical_simplify; tlsimpl; subst.
      all: destruct a_valid; [destruct H3; subst|]; cbn in Hpostc_tl; logical_simplify; subst; cbn.
      all: eauto.
      all: try (destruct (N.land a_address 4 =? 0) eqn:Haddr;
               ssplit; eauto;
               destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
      all: try (destruct count as [|[|[|]]]; [lia|..|lia]; cbn;
             ssplit; eauto;
             destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
      all: try (destruct H6; discriminate).
      all: try (destruct d_ready; logical_simplify; subst; cbn;
                  ssplit; eauto;
                  destruct x0 as [|? [|]]; cbn in *; try discriminate; reflexivity).
    - repeat destruct_one_match; rewrite ! length_replace; assumption.
  Qed.

  Lemma incr_output_correct : output_correct incr.
  Proof.
    intros ? **.
    simplify_spec incr. destruct input. destruct d0. destruct r as [[[? ?] ?] ?].
    apply I.
  Qed.

  Existing Instances incr_invariant_at_reset incr_invariant_preserved
           incr_output_correct.
  Global Instance incr_correctness : correctness_for incr.
  Proof. constructor; typeclasses eauto. Defined.
End Spec.
