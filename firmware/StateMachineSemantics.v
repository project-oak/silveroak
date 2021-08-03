Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth32.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

Module state_machine.
  Class parameters{word: word.word 32} :=
    { state : Type;
      register : Type;
      is_initial_state : state -> Prop;
      read_step (byte_count : nat) : state -> register -> word -> state -> Prop;
      write_step (byte_count : nat) : state -> register -> word -> state -> Prop;
      reg_addr : register -> word;
      isMMIOAddr : word -> Prop;
    }.

  Class ok{word: word.word 32}(M: parameters) :=
    { reg_addr_unique : forall r1 r2, reg_addr r1 = reg_addr r2 -> r1 = r2;
      read_step_isMMIOAddr : forall sz s r v s',
          read_step sz s r v s' -> forall a: word,
            word.unsigned (reg_addr r) <= word.unsigned a < word.unsigned (reg_addr r) + Z.of_nat sz ->
            isMMIOAddr a;
      write_step_isMMIOAddr : forall sz s r v s',
          write_step sz s r v s' -> forall a: word,
            word.unsigned (reg_addr r) <= word.unsigned a < word.unsigned (reg_addr r) + Z.of_nat sz ->
            isMMIOAddr a;
      read_step_is_aligned : forall sz s r v s',
          read_step sz s r v s' ->
          word.unsigned (reg_addr r) mod (Z.of_nat sz) = 0;
      write_step_is_aligned : forall sz s r v s',
          write_step sz s r v s' ->
          word.unsigned (reg_addr r) mod (Z.of_nat sz) = 0;
      read_step_size_valid : forall sz s r v s',
          read_step sz s r v s' ->
          List.In sz [1; 2; 4]%nat;
      write_step_size_valid : forall sz s r v s',
          write_step sz s r v s' ->
          List.In sz [1; 2; 4]%nat;
      read_step_bounded : forall sz s r v s',
          read_step sz s r v s' ->
          word.unsigned v < 2 ^ (Z.of_nat sz * 8);
      (* Note: It would be nice if we could allow too big writes and just ignore the upper
         bytes, but then we run into a specification issue: bedrock2 semantics of external
         calls (exec.interact) puts the whole unmodified word into the trace, and we want
         the trace of the risc-v machine to match the bedrock2 trace exactly (rather than
         introducing a notion of trace equivalence), but riscv-coq cannot put the upper
         ignored bits into the trace, because riscv.Spec.ExecuteI does not pass them
         to nonmem_store *)
      write_step_bounded : forall sz s r v s',
          write_step sz s r v s' ->
          word.unsigned v < 2 ^ (Z.of_nat sz * 8);
    }.
End state_machine.
Global Coercion state_machine.state : state_machine.parameters >-> Sortclass.

Section WithParameters.
  Import state_machine.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {M: state_machine.parameters} {M_ok: state_machine.ok M}.

  Definition step
             (action : string) (s : state) (args rets : list word) (s' : state)
    : Prop :=
    if String.prefix WRITE_PREFIX action
    then match args with
         | [addr;val] =>
           (exists r sz, reg_addr r = addr /\ rets = [] /\
                         access_size_to_MMIO_write sz = action /\ write_step sz s r val s')
         | _ => False
         end
    else if String.prefix READ_PREFIX action
         then match args with
              | [addr] => (exists r val sz, reg_addr r = addr /\ rets = [val] /\
                                            access_size_to_MMIO_read sz = action /\
                                            read_step sz s r val s')
              | _ => False
              end
         else False.

  (* Computes the Prop that must hold for this state to be accurate after the
     trace *)
  Fixpoint execution (t : trace) (s : state) : Prop :=
    match t with
    | [] => is_initial_state s
    | (_,action,args,(_,rets)) :: t =>
      exists prev_state,
      execution t prev_state
      /\ step action prev_state args rets s
    end.

  Global Instance ext_spec: ExtSpec := fun
             (t : trace)
             (mGive : mem)
             (action : string)
             (args: list word)
             (post: mem -> list word -> Prop) =>
    if String.prefix WRITE_PREFIX action
    then
      (exists r addr val sz,
          args = [addr;val]
          /\ mGive = map.empty
          /\ reg_addr r = addr
          /\ access_size_to_MMIO_write sz = action
          (* there must exist *at least one* possible state given this trace,
             and one possible transition given these arguments *)
          /\ (exists s s', execution t s /\ write_step sz s r val s')
          (* postcondition must hold for *all* possible states/transitions *)
          /\ (forall s s',
                execution t s ->
                write_step sz s r val s' ->
                post Interface.map.empty []))
       else if String.prefix READ_PREFIX action
            then
              (exists r addr sz,
                  args = [addr]
                  /\ mGive = map.empty
                  /\ reg_addr r = addr
                  /\ access_size_to_MMIO_read sz = action
                  (* there must exist *at least one* possible state given this
                     trace, and one possible transition given these arguments *)
                  /\ (exists s s' val, execution t s /\ read_step sz s r val s')
                  (* postcondition must hold for *all* possible states/transitions *)
                  /\ (forall s s' val,
                        execution t s ->
                        read_step sz s r val s' ->
                        post Interface.map.empty [val]))
               else False.

  Global Instance ext_spec_ok : ext_spec.ok ext_spec.
  Proof.
    split;
    cbv [ext_spec Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl];
    intros.
    all :
    repeat match goal with
           | H : context[String.prefix ?x ?y] |- _ =>
             destruct (String.prefix x y)
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           | H : _ :: _  = _ :: _ |- _ => inversion H; clear H; subst
           | H : access_size_to_MMIO_read ?sz1 = access_size_to_MMIO_read ?sz2 |- _ =>
             apply access_size_to_MMIO_read_inj in H; subst sz1
           | H: False |- _ => destruct H
           | H : reg_addr _ = reg_addr _ |- _ => apply reg_addr_unique in H
           | _ => progress subst
           end; eauto 20 using Properties.map.same_domain_refl.
  Qed.

  Lemma read_step_isMMIOAddr0: forall sz s a v s',
      read_step sz s a v s' -> isMMIOAddr (reg_addr a).
  Proof.
    intros. eapply read_step_isMMIOAddr. 1: exact H.
    apply read_step_size_valid in H. simpl in H. Lia.lia.
  Qed.

  Lemma write_step_isMMIOAddr0: forall sz s a v s',
      write_step sz s a v s' -> isMMIOAddr (reg_addr a).
  Proof.
    intros. eapply write_step_isMMIOAddr. 1: exact H.
    apply write_step_size_valid in H. simpl in H. Lia.lia.
  Qed.

End WithParameters.
