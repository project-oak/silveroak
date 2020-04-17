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

.PHONY: all coq auto_vcds clean

all:		coq auto_vcds adder_tree4_8_tb.vcd
xilinx:		adder8.vcd

VERILATOR = verilator +1800-2012ext+sv verilator.vlt
VLINT = $(VERILATOR) --lint-only

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

ExamplesSV:	ExamplesSV.hs
		ghc --make $^

nand2.sv:	coq ExamplesSV
		./ExamplesSV
		$(VLINT) nand2.sv
		$(VLINT) adder4.sv
		$(VLINT) fulladder.sv
		$(VLINT) loopedNAND.sv
		$(VLINT) pipelinedNAND.sv
		$(VLINT) adder8_3input.sv

testbench/adder_tree4_8_tb.sv:	nand2.sv

adder_tree4_8_tb.vcd: adder_tree4_8.sv testbench/adder_tree4_8_tb.sv
		$(VERILATOR) --trace --cc --top-module adder_tree4_8_tb testbench/adder_tree4_8_tb.sv adder_tree4_8.sv --exe testbench/adder_tree4_8_tb.cpp
		make -C obj_dir -f Vadder_tree4_8_tb.mk Vadder_tree4_8_tb
		obj_dir/Vadder_tree4_8_tb

%.vcd:		%.sv testbench/%_tb.sv
		iverilog -g2012 -o $*.vvp $^
		./$*.vvp

.PRECIOUS:	nand2.sv adder4.sv adder8_3input.sv \
		pipelinedNAND.sv loopedNAND.sv

auto_vcds:	nand2.vcd adder4.vcd adder8_3input.vcd \
		pipelinedNAND.vcd loopedNAND.vcd

fulladderFC.sv:	nand2.sv

fulladderFC.vcd:	fulladderFC.sv testbench/fulladderFC_tb.sv
			iverilog -y $(XILINX)/data/verilog/src/unisims -g2012 -o \
			  fulladderFC.vvp $^
			./fulladderFC.vvp

adder8.sv:	nand2.sv

adder8.vcd:	adder8.sv testbench/adder8_tb.sv
		xvlog -sv $^
		xelab --debug typical -L unisims_ver work.adder_test -s adder8_sim
		xsim --R adder8_sim

clean:
	-@$(MAKE) -f Makefile.coq clean
	git clean -xfd
	rm -rf obj_dir
