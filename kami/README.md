# Kami Experiments

This directory contains an attempt to use the [Kami](https://github.com/mit-plv/kami) system to specify a simple circuit and drive it through the point where we can generate a Verilog netlist which can be implemented and a Xilinx FPGA board and run.

The example we start with is a simple 4-bit counter [Counter.v](counter.v):
```
Require Import Kami.
Require Import Kami.Syntax.

Require Import Kami.Synthesize.
Require Import Ext.BSyntax.

Definition count := MethodSig ("counter" -- "count_value") (Bit 4) : Void.

Definition counter4 := MODULE {
    Register "counterReg" : Bit 4 <- $0

    with Rule "incrementAndOutput" :=
       Read val <- "counterReg";
       Write "counterReg" <- #val + ($1 :: Bit 4);
       (* Call count (#val); *)
       Retv

    with Method "count_value" () : (Bit 4) :=
       Read counterValue <- "counterReg";
       Ret #counterValue

  }.

Hint Unfold count : MethDefs.
Hint Unfold counter4 : ModuleDefs.

Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Definition targetCounter4 := ModulesSToBModules (getModuleS counter4).

Extraction "Counter4.ml" targetCounter4.
```

The extracted `Counter4.ml` program can be used with some other code to generate Bluespec, from which we can generate Verilog and then produce a circuit module for implementation on an FPGA (with a suitable wrapper for writing up the chip pins, dealing with the input clock etc.)