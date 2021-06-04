(* based on riscv.Platform.MetricRiscvMachine *)
Require Import Coq.Strings.String.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.RiscvMachine.

Notation Register := Z (only parsing).

Section Machine.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.
  Context {E: Type}. (* extra state (eg for devices) *)

  Record ExtraRiscvMachine := mkExtraRiscvMachine {
    getMachine :> RiscvMachine;
    getExtraState: E;
  }.

  Definition withExtraState : E -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun e '(mkExtraRiscvMachine m _) =>
            mkExtraRiscvMachine m e.

  Definition withRegs: Registers -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun regs2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withRegs regs2 mach) e).

  Definition withPc: word -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun pc2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withPc pc2 mach) e).

  Definition withNextPc: word -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun nextPC2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withNextPc nextPC2 mach) e).

  Definition withMem: Mem -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun mem2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withMem mem2 mach) e).

  Definition withXAddrs: XAddrs -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun xAddrs2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withXAddrs xAddrs2 mach) e).

  Definition withLog: list LogItem -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun log2 '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withLog log2 mach) e).

  Definition withLogItem: LogItem -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun item '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withLogItem item mach) e).

  Definition withLogItems: list LogItem -> ExtraRiscvMachine -> ExtraRiscvMachine :=
    fun items '(mkExtraRiscvMachine mach e) =>
      (mkExtraRiscvMachine (withLogItems items mach) e).

End Machine.
Arguments ExtraRiscvMachine {_} {_} {_} _.
