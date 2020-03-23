#
# Copyright 2020 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

.PHONY: cava all clean

all:		cava nand2.vcd adder4.vcd loopedNAND.vcd xorArrow.vcd loopedNandArrow.vcd

cava:		Makefile.coq FixupAscii
		$(MAKE) -f Makefile.coq
		./FixupAscii
		mv Ascii2.hs Ascii.hs
		runhaskell Setup.hs configure --user
		runhaskell Setup.hs build
		runhaskell Setup.hs install

Makefile.coq:
		coq_makefile -f _CoqProject -o Makefile.coq

FixupAscii:	FixupAscii.hs
		ghc --make FixupAscii.hs

ExamplesSV:	ExamplesSV.hs
		ghc --make ExamplesSV.hs

nand2.sv:	cava ExamplesSV
		./ExamplesSV
		verilator --lint-only verilator.vlt nand2.sv
		verilator --lint-only verilator.vlt adder4.sv
		verilator --lint-only verilator.vlt loopedNAND.sv
		verilator --lint-only verilator.vlt xorArrow.sv
		verilator --lint-only verilator.vlt loopedNAND.sv
		verilator --lint-only verilator.vlt loopedNandArrow.sv

nand2.vcd:	nand2.sv nand2_tb.sv
		iverilog -g2012 -o nand2.vvp nand2.sv nand2_tb.sv
		./nand2.vvp

adder4.sv:	nand2.sv

adder4.vcd:	adder4.sv adder4_tb.sv
		iverilog -g2012 -o adder4.vvp adder4.sv adder4_tb.sv
		./adder4.vvp

xorArrow.sv:	nand2.sv

xorArrow.vcd:	xorArrow.sv xorArrow_tb.sv
		iverilog -g2012 -o xorArrow.vvp xorArrow.sv xorArrow_tb.sv
		./xorArrow.vvp

loopedNAND.sv:	nand2.sv

loopedNAND.vcd:	loopedNAND.sv loopedNAND_tb.sv
		iverilog -g2012 -o loopedNAND.vvp loopedNAND.sv loopedNAND_tb.sv
		./loopedNAND.vvp

loopedNandArrow.sv:	nand2.sv

loopedNandArrow.vcd:	loopedNandArrow.sv loopedNandArrow_tb.sv
			iverilog -g2012 -o loopedNandArrow.vvp loopedNandArrow.sv loopedNandArrow_tb.sv
			./loopedNandArrow.vvp

clean:
		-$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq .Makefile.coq.conf \
                       *.hi *.o ExamplesSV FixupAscii dist work-obj93.cf
		xargs rm -rf < .gitignore
		rm -rf Cava/.*.aux

