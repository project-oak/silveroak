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

* The [Coq proof assistant](https://coq.inria.fr/) version 8.11.0.
* The [coq-ext-lib](https://github.com/coq-community/coq-ext-lib) library for Coq.
* The [GHC Haskell compiler](https://www.haskell.org/ghc/) version 8.6.5 or later
* The [Icarus Verilog](http://iverilog.icarus.com/) circuit simulator version
  11.0 or later. GitHub link:
  [https://github.com/steveicarus/iverilog](https://github.com/steveicarus/iverilog)
* [Verilator](https://www.veripool.org/wiki/verilator) version 4.028 (as specified by the
  [OpenTitan](https://docs.opentitan.org/doc/ug/install_instructions/#verilator) documentation).

## Building

Type `make` in the directory `cava`:

```console
$ cd oak-hardware/cava
$ make
```

To remove all automatically generated files:
```console
$ make clean
```

## Cava Examples (monadic versions)
See [Cava Examples](https://github.com/project-oak/oak-hardware/tree/master/cava/monad-examples/README.md) for a few examples of circuits described in Cava, proofs about their behaviour and extraction to SystemVerilog circuits for simulation and FPGA implementation.

