# Cava: Lava-style circuits in Coq

This is a work in progress attempt to encode Lava-style gate-level circuit
descriptions in Coq for circuit specification, formal verification and
extraction into VHDL or SystemVerilog for implementation on FPGAs. The code
is currently very experimental and in constant flux.

Please see the [contributing guide](CONTRIBUTING.md) for how to submit push
requests.

## Pre-requisites

### Nix

If you have the [Nix package manager](https://nixos.org/nix/) installed, you can
simply run `nix-shell` from the `oak-hardware/cava` directory. Coq, Haskell, and
Icarus Verilog will then be available in your `$PATH`.

### Non-Nix

Please install the following components:

* The [Coq proof assistant](https://coq.inria.fr/) version 8.9.2 or later
* The [coq-ext-lib](https://github.com/coq-community/coq-ext-lib) library for Coq.
* The [GHC Haskell compiler](https://www.haskell.org/ghc/) version 8.6.5 or later
* The [Icarus Verilog](http://iverilog.icarus.com/) circuit simulator version
  11.0 or later. GitHub link:
  [https://github.com/steveicarus/iverilog](https://github.com/steveicarus/iverilog)

## Building

Do a `make` in these directories:

```bash
$ cd oak-hardware/cava
$ make
$ cd ../cava-examples
$ make
```

If all worked well you should find an automatically generated
SystemVerilog file called `fulladder.sv` in the `cava-examples` directory which should have contents like:

```verilog
module fulladder(
  input logic cin,
  input logic b,
  input logic a,
  output logic carry,
  output logic sum
  );

  timeunit 1ns; timeprecision 1ns;

  logic[9:0] net;

  // Constant nets
  assign net[0] = 1'b0;
  assign net[1] = 1'b1;
  // Wire up inputs.
  assign net[4] = cin;
  assign net[3] = b;
  assign net[2] = a;
  // Wire up outputs.
  assign carry = net[9] ;
  assign sum = net[7] ;

  or inst9 (net[9],net[6],net[8]);
  and inst8 (net[8],net[5],net[4]);
  xor inst7 (net[7],net[5],net[4]);
  and inst6 (net[6],net[2],net[3]);
  xor inst5 (net[5],net[2],net[3]);

endmodule

```

A few other SystemVerilog files will also be generated.

## Cava Examples
See [Cava Examples](https://github.com/project-oak/oak-hardware/tree/master/cava-examples/README.md) for a
few examples of circuits described in Cava, proofs about their behavioiur and
extraction to SystemVerilog circuis for simulation and FPGA implementation.

## Nand Game Examples
Some of the circuits described on the [Nand Game]((http://nandgame.com/)) web page have
been implemented in Cava, along with proofs about correct operation, which
are available at the [Cava Nand Game Examples](https://github.com/project-oak/oak-hardware/tree/master/nandgame/README.md) page.
