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

# To simulate Xilinx specific SystemVerilog netlists the environment
# variable XILINX should point to the root of the Xilinx software
# tools installation directory e.g.
#    ...../vivado/2018.3 

.PHONY: all compile clean

all:		compile nand2.sv nand2.vcd pipelinedNAND.vcd
xilinx:		adder8.vcd

Makefile.coq:
		coq_makefile -f _CoqProject -o Makefile.coq

compile:	Makefile.coq
		$(MAKE) -f Makefile.coq

ExamplesSV:	ExamplesSV.hs
		ghc --make ExamplesSV.hs

nand2.sv:	compile ExamplesSV
		./ExamplesSV
		verilator --lint-only verilator.vlt nand2.sv
		verilator --lint-only verilator.vlt fulladder.sv
		verilator --lint-only verilator.vlt pipelinedNAND.sv
		verilator --lint-only verilator.vlt adder8_3in.sv

nand2.vcd:	nand2.sv nand2_tb.sv
		iverilog -g2012 -o nand2.vvp nand2.sv nand2_tb.sv
		./nand2.vvp 

fulladderFC.sv:	nand2.sv

fulladderFC.vcd:	fulladderFC.sv fulladderFC_tb.sv
			iverilog -y $(XILINX)/data/verilog/src/unisims -g2012 -o \
			  fulladderFC.vvp fulladderFC.sv fulladderFC_tb.sv
			./fulladderFC.vvp

adder8.sv:	nand2.sv

adder8.vcd:	adder8.sv adder8_tb.sv
		xvlog -sv adder8.sv adder8_tb.sv
		xelab --debug typical -L unisims_ver work.adder_test -s adder8_sim
		xsim --R adder8_sim

adder8_3in.sv:	nand2.sv

adder8_3in.vcd:	adder8_3in.sv adder8_3in_tb.sv
		iverilog -g2012 -o adder8_3in.vvp adder8_3in.sv adder8_3in_tb.sv
		./adder8_3in.vvp

pipelinedNAND.sv:	nand2.sv

pipelinedNAND.vcd:	pipelinedNAND.sv pipelinedNAND_tb.sv
			iverilog -g2012 -o pipelinedNAND.vvp pipelinedNAND.sv pipelinedNAND_tb.sv
			./pipelinedNAND.vvp

clean:
		rm -rf  *.v.d *.vo *.o *.hi .*.aux *.glob \
		        xsim.dir xvhdl.pb xvhdl.log Makefile.coq Makefile.coq.conf \
			FixupAscii ExamplesSV \
			nand2.sv fulladder.sv nand2.vcd fulladderFC.vcd adder8.vcd *.vvp \
			pipelinedNAND.sv pipelinedNAND.vcd \
			*.jou *.wdb *.log *.pb .Makefile.coq.d *.vok *.vos
		xargs rm -rf < .gitignore

