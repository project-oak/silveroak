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

.PHONY: all coq clean

SV = lut1_inv.sv lut2_and.sv lut3_mux.sv lut4_and.sv lut5_and.sv \
     lut6_and.sv

BENCHES = $(SV:.sv=_tb.sv)
CPPS = $(SV:.sv=_tb.cpp)
VCDS = $(SV:.sv=_tb.vcd)

all:		coq $(VCDS)
extraction:	$(SV)

VERILATOR = verilator +1800-2012ext+sv verilator.vlt -y $(XILINX)/data/verilog/src/xeclib
VLINT = $(VERILATOR) --lint-only

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

VivadoTestsSV:	coq VivadoTestsSV.hs
		ghc -O2 --make VivadoTestsSV.hs
		./VivadoTestsSV

$(SV) $(BENCHES) $(VCDS):	coq VivadoTestsSV

%_tb.vcd:	%.sv %_tb.sv %_tb.cpp
		$(VERILATOR) --trace --cc --top-module $*_tb $*_tb.sv $*.sv --exe $*_tb.cpp
		make -C obj_dir -f V$*_tb.mk V$*_tb
		obj_dir/V$*_tb

%_tb_xsim.vcd:	%.sv
		xvlog -sv $*.sv $*_tb.sv
		xelab --debug typical -L unisims_ver work.$*_tb -s $*_tb_sim
		xsim --tclbatch $*_tb.tcl $*_tb_sim
		mv $*_tb.vcd $@

clean:
	-@$(MAKE) -f Makefile.coq clean
	git clean -Xfd
	rm -rf obj_dir
