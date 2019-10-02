# Cava: Lava-style circuits in Coq

This is a work in progress attempt to encode Lava-style gate-level circuit descriptions
in Coq for circuit specification, formal verification and extraction into VHDL or
Verilog for implementation on FPGAs.

Cava provides a deep embedding for Lava-like circuits in Coq with
combinators to compose circuits. For example, a toy pipelined NAND gate
build from and AND gate and an inverter is described file the file
[Nand2.v](Nand2.v):

```
Definition nand2_pipelined := Delay ∘ Inv ∘ Delay ∘ And2.
```
