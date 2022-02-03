# Silver Oak

Silver Oak is a research project at Google Research exploring alternative
techniques for producing high assurance circuits and systems based on an
approach that unifies specification, implementation and formal verification
in a single system, specifically the [Coq](https://coq.inria.fr/) interactive
theorem prover. We follow an approach inspired by the vision set out by
[Adam Chlipala](http://adam.chlipala.net/) at MIT in his book
[Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/).

The Silver Oak project focuses on the design and verification of high assurance variants
of some of the peripherals used in the [OpenTitan](https://opentitan.org/) silicon root of trust e.g.
the AES crypto-accelerator block. We focus on the specification, implementation
and verification of low-level structural circuits built bottom up by composing
basic circuit elements (gates, registers, wires) using powerful higher order
combinators in the style of [Lava](https://dl.acm.org/doi/abs/10.1145/291251.289440).
Another Coq-based approache for producing hardware is
[Kami](https://plv.csail.mit.edu/kami/) which encodes aspects of the
[Bluespec](http://wiki.bluespec.com/) hardware description language as a EDSL in Coq.
Kami and Bluespec are powerful tools for designing processor-style control-orientated
circuits. We focus instead on "network-style" and "daatpath" low level circuits
e.g. hardware accelerators for AES.

A key design goal for our project is to produce hardware which are just as
efficient as the existing blocks written by hardware engineers in SystemVerilog.
Consequently our design decisions focus on giving the designer a lot of
control over the generated circuit netlist by using high level combinators
to make low level circuit design more productive and more ameanble to
formal verification. The EDSL we are developing for this task is called
Cava (Coq + Lava).

Our verification work is focused on specification and verification of
circuit designs (i.e. "programs") and not currently on the "compiler" i.e.
the infrastructure that maps form Cava EDSL in Coq to SystemVerilog. Complementary
work is under way at other research groups that tackle the compiler
verification challenge for hardware RTL synthesis to gates e.g.
[Verified Compilation on a Verified Processor](https://ts.data61.csiro.au/publications/csiro_full_text/Loeoew_KTMNAF_19.pdf).

## The Code

The code is currently very experimental and in constant flux! Please see the [contributing guide](CONTRIBUTING.md) for how to submit push
requests.

## Pre-requisites

Please install the following components:

* The [Coq proof assistant](https://coq.inria.fr/) version 8.13.0.
* The [GHC Haskell compiler](https://www.haskell.org/ghc/) version 8.6 or later (note that if you install the [Haskell Platform](https://www.haskell.org/platform/) then you get Cabal, too).
* [Cabal](https://www.haskell.org/cabal/) version 3.0.0.0 or later.
* [Verilator](https://www.veripool.org/wiki/verilator) version 4.104 (as specified by the
  [OpenTitan](https://docs.opentitan.org/doc/ug/install_instructions/#verilator) documentation).

To re-build the OpenTitan system with the Cava versions of the high assurance
peripherals you will also need to install
[OpenTitan](https://github.com/lowRISC/opentitan/blob/master/README.md). You
can follow the instructions
[here](https://docs.opentitan.org/doc/ug/getting_started_verilator/).

## Building

To build the Cava system and its examples and run tests, type `make` in the root directory of the repo.

```console
$ cd silveroak
$ git submodule update --init --recursive
$ make
```

To remove all automatically generated files (this may be needed after upgrading Coq, for example):
```console
$ make cleanall
```

To remove files generated as part of `silveroak`, but leave dependencies' in-tree compilation artifacts:
```console
$ make clean
```

## Updating git submodules

Although infrequent, commits may update the git submodules used by this project.
Git does not automatically update submodules, and so to cleanly update submodule
dependencies run the `make update-third_party` rule.

```console
$ cd silveroak
$ make update-third_party
```

or equivalently

```console
$ cd silveroak
$ git submodule update --init --recursive
$ make cleanall
```

## Building documentation

Documentation is either in automatically-built `.md` files under `docs/`, or in
Coq files under `demos/` that are converted to HTML using the Alectryon tool.
To build these Alectryon files, you need to install Alectryon as an optional
dependency. The procedure is:

- Install [alectryon](https://github.com/cpitclaudel/alectryon) dependencies
  following their README
- Clone alectryon
- Set an environment variable `ALECTRYON_PATH` to the path to your clone
- Call `make html` from the `demos/` directory

## Cava Examples
See [Cava Examples](https://github.com/project-oak/silveroak/blob/main/examples/README.md) for a few examples of circuits described in Cava, proofs about their behaviour and extraction to SystemVerilog circuits for simulation and FPGA implementation.

