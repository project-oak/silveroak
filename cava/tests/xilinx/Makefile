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

all:		coq lut1_inv_tb.vcd lut2_and_tb.vcd

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

VivadoTestsSV:	VivadoTestsSV.hs
		ghc -O2 --make $^

lut1_inv_tb.sv:	coq VivadoTestsSV
		./VivadoTestsSV

lut1_inv_tb.vcd:	lut1_inv.sv lut1_inv_tb.sv lut1_inv_tb.tcl
			vivado -mode tcl -source lut1_inv_tb.tcl
			mv lut1_inv/lut1_inv.sim/sim_1/behav/xsim/lut1_inv_tb.vcd .

clean:
	-@$(MAKE) -f Makefile.coq clean
	git clean -xfd
	rm -rf obj_dir
