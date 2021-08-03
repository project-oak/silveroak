(* Copied from riscv.Platform.MinimalMMIO, but adapted to log how many bits were
   MMIO'd, which makes it incompatible with the Kami processor, whose connection
   proof to riscv would take some time to update.
   Also, should the trace contain zero-extended or sign-extended values?
   Ideally, it would only contain the number of bytes read/written rather than a
   whole word, but that's not compatible with how everything is set up.
   Sign-extending depending on whether Lb or Lbu was used doesn't make sense
   because that's not visible to the device, Lb vs Lbu only affects what the
   processor does after obtaining the value, when placing it in a register.
   So we choose to zero-extend in this file.
   And another difference is that here we add MMIOWriteOK and assert it in
   nonmem_store, so that even if the postcondition is as weak as (fun _ => True),
   we know that only valid state machine interactions were made. *)
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Export riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.ListSet.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MaterializeRiscvProgram.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Class MMIOSpec{W: Words} {Mem : map.map word byte} := {
  (* should not say anything about alignment, just whether it's in the MMIO range *)
  isMMIOAddr: word -> Prop;

  (* alignment and load size checks *)
  isMMIOAligned: nat -> word -> Prop;

  (* hardware guarantees on MMIO read values *)
  MMIOReadOK : nat -> list LogItem -> word -> word -> Prop;

  (* hardware requirements on which MMIO writes are acceptable *)
  MMIOWriteOK : nat -> list LogItem -> word -> word -> Prop;
}.

Definition natToStr(n: nat): string := DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Section Riscv.
  Import free.
  Context {W: Words} {Mem: map.map word byte} {Registers: map.map Register word}.

  Definition mmioLoadEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, ("MMIOREAD" ++ natToStr (n * 8))%string, [addr]),
     (map.empty, [word.of_Z (LittleEndian.combine n v)])).

  Definition mmioStoreEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, ("MMIOWRITE" ++ natToStr (n * 8))%string,
      [addr; word.of_Z (LittleEndian.combine n v)]), (map.empty, [])).

  Context {mmio_spec: MMIOSpec}.

  Definition nonmem_store(n: nat)(ctxid: SourceType) a v mach post :=
    isMMIOAddr a /\ isMMIOAligned n a /\
    MMIOWriteOK n (getLog mach) a (word.of_Z (LittleEndian.combine n v)) /\
    post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs))
         (withLogItem (@mmioStoreEvent a n v)
         mach)).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach))
    | None => nonmem_store n ctxid a v mach post
    end.

  Definition nonmem_load(n: nat)(ctxid: SourceType) a mach (post: _ -> _ -> Prop) :=
    isMMIOAddr a /\ isMMIOAligned n a
    (* there exists at least one valid MMIO read value (set is nonempty) *)
    /\ (exists v, MMIOReadOK n (getLog mach) a (word.of_Z (LittleEndian.combine n v)))
    (* ...and postcondition holds for all valid read values *)
    /\ forall v,
        MMIOReadOK n (getLog mach) a (word.of_Z (LittleEndian.combine n v)) ->
        post v (withLogItem (@mmioLoadEvent a n v) mach).

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach post
    end.

  Definition updatePc(mach: RiscvMachine): RiscvMachine :=
    withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach).

  Definition interpret_action (a : riscv_primitive) (mach : RiscvMachine) :
    (primitive_result a -> RiscvMachine -> Prop) -> (RiscvMachine -> Prop) -> Prop :=
    match a with
    | GetRegister reg => fun (postF: word -> RiscvMachine -> Prop) postA =>
        let v :=
          if Z.eq_dec reg 0 then word.of_Z 0
          else match map.get mach.(getRegs) reg with
               | Some x => x
               | None => word.of_Z 0 end in
        postF v mach
    | SetRegister reg v => fun postF postA =>
      let regs := if Z.eq_dec reg Register0
                  then mach.(getRegs)
                  else map.put mach.(getRegs) reg v in
      postF tt (withRegs regs mach)
    | GetPC => fun postF postA => postF mach.(getPc) mach
    | SetPC newPC => fun postF postA => postF tt (withNextPc newPC mach)
    | LoadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | LoadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | LoadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | LoadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | StoreByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | StoreHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | StoreWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | StoreDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | EndCycleNormal => fun postF postA => postF tt (updatePc mach)
    | EndCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | GetCSRField _
    | SetCSRField _ _
    | GetPrivMode
    | SetPrivMode _
    | Fence _ _
        => fun postF postA => False
    end.

  Definition MinimalMMIOPrimitivesParams:
    PrimitivesParams (free riscv_primitive primitive_result) RiscvMachine :=
  {|
    Primitives.mcomp_sat A m mach postF :=
      @free.interpret _ _ _ interpret_action A m mach postF (fun _ => False);
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
    Primitives.valid_machine mach :=
      map.undef_on mach.(getMem) isMMIOAddr /\ disjoint (of_list mach.(getXAddrs)) isMMIOAddr;
  |}.

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load nonmem_load].
    destruct (Memory.load_bytes n (getMem m) a); intuition eauto.
  Qed.

  Lemma store_weaken_post n c a v m (post1 post2:_->Prop)
    (H: forall s, post1 s -> post2 s)
    : store n c a v m post1 -> store n c a v m post2.
  Proof.
    cbv [store nonmem_store].
    destruct (Memory.store_bytes n (getMem m) a); intuition eauto.
  Qed.

  Lemma interpret_action_weaken_post a (postF1 postF2: _ -> _ -> Prop) (postA1 postA2: _ -> Prop):
    (forall r s, postF1 r s -> postF2 r s) ->
    (forall s, postA1 s -> postA2 s) ->
    forall s, interpret_action a s postF1 postA1 -> interpret_action a s postF2 postA2.
  Proof.
    destruct a; cbn; try solve [intuition eauto].
    all : eauto using load_weaken_post, store_weaken_post.
  Qed.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MinimalMMIOPrimitivesParams Bind Return Monad_free].
    { symmetry. eapply interpret_bind_ex_mid, interpret_action_weaken_post. }
    { symmetry; intros. rewrite interpret_ret; eapply iff_refl. }
  Qed.

  Lemma preserve_undef_on{memOk: map.ok Mem}: forall n (m m': Mem) a w s,
      Memory.store_bytes n m a w = Some m' ->
      map.undef_on m s ->
      map.undef_on m' s.
  Proof.
    eauto using map.same_domain_preserves_undef_on, Memory.store_bytes_preserves_domain.
  Qed.

  Lemma interpret_action_total{memOk: map.ok Mem} a s postF postA :
    map.undef_on s.(getMem) isMMIOAddr ->
    disjoint (of_list s.(getXAddrs)) isMMIOAddr ->
    interpret_action a s postF postA ->
    exists s', map.undef_on s'.(getMem) isMMIOAddr /\
          disjoint (of_list s'.(getXAddrs)) isMMIOAddr /\
          (postA s' \/ exists v', postF v' s').
  Proof.
    destruct s, a; cbn -[HList.tuple];
      cbv [load store nonmem_load nonmem_store]; cbn -[HList.tuple];
        repeat destruct_one_match;
        intuition idtac;
        repeat lazymatch goal with
               | H : postF _ ?mach |- exists _ : RiscvMachine, _ =>
                 exists mach; cbn [RiscvMachine.getMem RiscvMachine.getXAddrs]
               | H : postA ?mach |- exists _ : RiscvMachine, _ =>
                 exists mach; cbn [RiscvMachine.getMem RiscvMachine.getXAddrs]
               | Hexists : (exists v, ?P), Hforall : (forall v, ?P -> _) |- _ =>
                 let v := fresh "v" in
                 destruct Hexists as [v Hexists];
                   specialize (Hforall v Hexists)
               end;
        ssplit; eauto; simpl;
        change removeXAddr with (@List.removeb word word.eqb _);
        rewrite ?ListSet.of_list_removeb;
        intuition eauto 10 using preserve_undef_on, disjoint_diff_l.
  Qed.

  Lemma interpret_action_total'{memOk: map.ok Mem} a s post :
    map.undef_on s.(getMem) isMMIOAddr ->
    disjoint (of_list s.(getXAddrs)) isMMIOAddr ->
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    exists v s', post v s' /\ map.undef_on s'.(getMem) isMMIOAddr
                           /\ disjoint (of_list s'.(getXAddrs)) isMMIOAddr.
  Proof.
    intros. pose proof interpret_action_total as P.
    specialize P with (postA := (fun _ : RiscvMachine => False)). simpl in P.
    specialize (P _ _ _ H H0 H1).
    destruct P as (s' & ? & ? & ?).
    destruct H4 as [[] | (v' & ?)].
    eauto.
  Qed.

  Import coqutil.Tactics.Tactics.

  Lemma interpret_action_appendonly a s postF postA :
    interpret_action a s postF postA ->
    interpret_action a s (fun _ s' => endswith s'.(getLog) s.(getLog))
                           (fun s' => endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store nonmem_load nonmem_store]; cbn;
      repeat destruct_one_match;
      intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  (* NOTE: maybe instead a generic lemma to push /\ into postcondition? *)
  Lemma interpret_action_appendonly' a s postF postA :
    interpret_action a s postF postA ->
    interpret_action a s (fun v s' => postF v s' /\ endswith s'.(getLog) s.(getLog))
                         (fun   s' => postA   s' /\ endswith s'.(getLog) s.(getLog)).
  Proof.
    destruct s, a; cbn; cbv [load store nonmem_load nonmem_store]; cbn;
      repeat destruct_one_match; intros; destruct_products; try split;
        intuition eauto using endswith_refl, endswith_cons_l.
  Qed.

  Lemma interpret_action_appendonly'' a s post :
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    interpret_action a s (fun v s' => post v s' /\ endswith s'.(getLog) s.(getLog))
                         (fun _ : RiscvMachine => False).
  Proof.
    intros. pose proof interpret_action_appendonly' as P.
    specialize (P _ _ _ (fun _ : RiscvMachine => False) H). simpl in P.
    eapply interpret_action_weaken_post. 3: exact P. all: simpl; intuition eauto.
  Qed.

  Lemma interpret_action_preserves_valid{memOk: map.ok Mem} a s postF postA :
    map.undef_on s.(getMem) isMMIOAddr ->
    disjoint (of_list s.(getXAddrs)) isMMIOAddr ->
    interpret_action a s postF postA ->
    interpret_action a s (fun v s' => postF v s' /\
                                      map.undef_on s'.(getMem) isMMIOAddr /\
                                      disjoint (of_list s'.(getXAddrs)) isMMIOAddr)
                         (fun s' => postA s' /\
                                    map.undef_on s'.(getMem) isMMIOAddr /\
                                    disjoint (of_list s'.(getXAddrs)) isMMIOAddr).
  Proof.
    destruct s, a; cbn; cbv [load store nonmem_load nonmem_store]; cbn;
      repeat destruct_one_match; intros; destruct_products; try split;
        change removeXAddr with (@List.removeb word word.eqb _);
        rewrite ?ListSet.of_list_removeb;
        intuition eauto 10 using preserve_undef_on, disjoint_diff_l.
  Qed.

  Lemma interpret_action_preserves_valid'{memOk: map.ok Mem} a s post :
    map.undef_on s.(getMem) isMMIOAddr ->
    disjoint (of_list s.(getXAddrs)) isMMIOAddr ->
    interpret_action a s post (fun _ : RiscvMachine => False) ->
    interpret_action a s (fun v s' => post v s' /\ map.undef_on s'.(getMem) isMMIOAddr /\
                                      disjoint (of_list s'.(getXAddrs)) isMMIOAddr)
                         (fun _ : RiscvMachine => False).
  Proof.
    intros. pose proof interpret_action_preserves_valid as P.
    specialize (P _ _ _ (fun _ : RiscvMachine => False) H H0 H1). simpl in P.
    eapply interpret_action_weaken_post. 3: exact P. all: simpl; intuition eauto.
  Qed.

  Global Instance MinimalMMIOPrimitivesSane{memOk: map.ok Mem} :
    PrimitivesSane MinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane valid_machine MinimalMMIOPrimitivesParams]; intros *; intros [U D] M;
      (split; [ exact (interpret_action_total' _ st _ U D M)
              | eapply interpret_action_preserves_valid'; try eassumption;
                eapply interpret_action_appendonly''; try eassumption ]).
  Qed.

  Global Instance MinimalMMIOSatisfiesPrimitives{memOk: map.ok Mem} :
    Primitives MinimalMMIOPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MinimalMMIOPrimitivesParams invalidateWrittenXAddrs].
    all: intros;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple]
      | _ => progress cbv [valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || blia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct initialL; eassumption.
  Qed.

End Riscv.
