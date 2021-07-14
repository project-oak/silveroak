Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

Module parameters.
  Class parameters
        {width} {word : Interface.word.word width}
        {mem : Interface.map.map word Byte.byte} :=
    { state : Type;
      register : Type;
      is_initial_state : state -> Prop;
      read_step : state -> register -> word -> state -> Prop;
      write_step : state -> register -> word -> state -> Prop;
      reg_addr : register -> word;
      is_reg_addr : word -> Prop;
    }.
  Global Arguments parameters : clear implicits.

  Class ok {width word mem} (p : parameters width word mem) :=
    { width_ok : width = 32 \/ width = 64;
      word_ok : word.ok word; (* for impl of mem below *)
      mem_ok : Interface.map.ok mem; (* for impl of mem below *)
      reg_addr_unique : forall r1 r2, reg_addr r1 = reg_addr r2 -> r1 = r2;
      reg_addrs_aligned :
        forall a, is_reg_addr a -> word.unsigned a mod (bytes_per_word width) = 0;
      reg_addrs_small :
        forall a, is_reg_addr a -> word.unsigned a + bytes_per_word width <= 2 ^ width;
      read_step_is_reg_addr : forall s a v s', read_step s a v s' -> is_reg_addr (reg_addr a);
      write_step_is_reg_addr : forall s a v s', write_step s a v s' -> is_reg_addr (reg_addr a);
    }.
End parameters.
Notation parameters := parameters.parameters.

(* read and write interaction names *)
Definition READ := "MMIOREAD".
Definition WRITE := "MMIOWRITE".

Section WithParameters.
  Import parameters.
  Context {width word mem} {p : parameters width word mem}
          {p_ok : parameters.ok p}.

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

  Definition step
             (action : string) (s : state) (args rets : list word) (s' : state)
    : Prop :=
    if String.eqb action WRITE
    then match args with
         | [addr;val] =>
           (exists r, reg_addr r = addr /\ rets = [] /\ write_step s r val s')
         | _ => False
         end
    else if String.eqb action READ
         then match args with
              | [addr] => (exists r val, reg_addr r = addr /\ rets = [val] /\ read_step s r val s')
              | _ => False
              end
         else False.

  (* Computes the Prop that must hold for this state to be accurate after the
     trace *)
  Fixpoint execution (t : bedrock2_trace) (s : state) : Prop :=
    match t with
    | [] => is_initial_state s
    | (_,action,args,(_,rets)) :: t =>
      exists prev_state,
      execution t prev_state
      /\ step action prev_state args rets s
    end.

  Definition ext_spec (t : bedrock2_trace)
             (mGive : mem)
             (action : string)
             (args: list word)
             (post: mem -> list word -> Prop) :=
    if String.eqb action WRITE
    then
      (exists r addr val,
          args = [addr;val]
          /\ mGive = map.empty
          /\ reg_addr r = addr
          (* there must exist *at least one* possible state given this trace,
             and one possible transition given these arguments *)
          /\ (exists s s', execution t s /\ write_step s r val s')
          (* postcondition must hold for *all* possible states/transitions *)
          /\ (forall s s',
                execution t s ->
                write_step s r val s' ->
                post Interface.map.empty []))
       else if String.eqb action READ
            then
              (exists r addr,
                  args = [addr]
                  /\ mGive = map.empty
                  /\ reg_addr r = addr
                  (* there must exist *at least one* possible state given this
                     trace, and one possible transition given these arguments *)
                  /\ (exists s s' val, execution t s /\ read_step s r val s')
                  (* postcondition must hold for *all* possible states/transitions *)
                  /\ (forall s s' val,
                        execution t s ->
                        read_step s r val s' ->
                        post Interface.map.empty [val]))
               else False.

  Global Instance semantics_parameters  : Semantics.parameters :=
    {|
    Semantics.width := width;
    Semantics.word := word;
    Semantics.mem := mem;
    Semantics.locals := SortedListString.map _;
    Semantics.env := SortedListString.map _;
    Semantics.ext_spec := ext_spec;
    |}.

  Global Instance ext_spec_ok : ext_spec.ok _.
  Proof.
    split;
    cbv [ext_spec Semantics.ext_spec semantics_parameters
    Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl
    ];
    intros.
    all :
    repeat match goal with
           | H : context[(?x =? ?y)%string] |- _ =>
             destruct (x =? y)%string in *
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           | H : _ :: _  = _ :: _ |- _ => inversion H; clear H; subst
           | H: False |- _ => destruct H
           | H : reg_addr _ = reg_addr _ |- _ => apply reg_addr_unique in H
           | _ => progress subst
           end; eauto 20 using Properties.map.same_domain_refl.
  Qed.

  Global Instance ok : Semantics.parameters_ok semantics_parameters.
  Proof.
    split; cbv [env locals semantics_parameters]; try exact _.
    { exact width_ok. }
    { exact word_ok. }
    { exact mem_ok. }
    { exact (SortedListString.ok _). }
    { exact (SortedListString.ok _). }
  Defined.

  (* COPY-PASTE this *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
End WithParameters.
