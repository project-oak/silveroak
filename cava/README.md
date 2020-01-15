# Cava: Lava-style circuits in Coq

This is a work in progress attempt to encode Lava-style gate-level circuit
descriptions in Coq for circuit specification, formal verification and
extraction into VHDL or SystemVerilog for implementation on FPGAs. The code
is currently very experimental and in constant flux.

Please see the [contributing guide](CONTRIBUTING.md) for how to submit push
requests.

## Pre-requisites
Please install the following components:

* The [GHC Haskell compiler](https://www.haskell.org/ghc/).
* The [Icarus Verilog](https://www.haskell.org/ghc/) circuit simulator.

Cava uses an open-source Coq library that provides some useful Haskell
inspired idioms. This should be installed as a sibling directory to
the oak-hardware directory.

```bash
$ git clone https://github.com/jwiegley/coq-haskell.git
$ git clone https://github.com/project-oak/oak-hardware.git
```

Do a make in these directories:

```bash
$ cd coq-haskell
$ make
$ cd ../oak-hardware/cava
$ make
$ cd ../cava-examples
$ make
```

If all worked well you should find an automatically generated
SystemVerilog file called fulladder.sv which should have
contents like:

```verilog
module fulladder(
  input logic cin,
  input logic b,
  input logic a,
  output logic carry,
  output logic sum
  );

  logic[0:7] net;

  // Wire up inputs.
  assign net[2] = cin;
  assign net[1] = b;
  assign net[0] = a;
  // Wire up outputs.
  assign carry = net[7] ;
  assign sum = net[5] ;

  or inst7 (net[7],net[4],net[6]);
  and inst6 (net[6],net[3],net[2]);
  xor inst5 (net[5],net[3],net[2]);
  and inst4 (net[4],net[0],net[1]);
  xor inst3 (net[3],net[0],net[1]);

endmodule
```

A few other SystemVerilog files will also be generated.