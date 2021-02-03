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

# To produce the SystemVerilog AES implementation files and their
# associated test artifcats do:
#
# $ make
#
# To run FPGA implementation of the AES subcomponents and generate
# utilization reports do:
#
# $ make util
#
# The resulting implementations will be in the aes_implementation directory.
# This step will require the installation of the Xilinx Vivado
# FPAG design tools.

.PHONY: all coq minimize-requires clean _CoqProject

SV = aes_mix_columns.sv

BENCHES = $(SV:.sv=_tb.sv)
CPPS = $(SV:.sv=_tb.cpp)
VCDS = $(SV:.sv=_tb.vcd)

.PRECIOUS: $(VCDS)

all:		coq $(VCDS)
util:		aes_sub_bytes_util aes_mix_columns_util

VERILATOR = verilator +1800-2012ext+sv verilator.vlt
VLINT = $(VERILATOR) --lint-only

_CoqProject:
		@echo "INSTALLDEFAULTROOT = AcornAes" > _CoqProject
		@echo "-R . AcornAes" >> _CoqProject
		@echo "-R ../Spec AesSpec" >> _CoqProject
		@echo "-R ../../../cava/Cava Cava" >> _CoqProject
		@echo "-R ../../../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../../../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		git ls-files | grep "\.v$$" >> _CoqProject

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

AESSV:		coq AESSV.hs
		ghc --make AESSV.hs
		./AESSV

minimize-requires: coq
	../../../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

$(SV) $(BENCHES) $(CPPS):	coq AESSV

obj_dir/V%_tb:	%.sv %_tb.sv %_tb.cpp
		$(VERILATOR) --trace --cc --top-module $*_tb $*_tb.sv $*.sv --exe $*_tb.cpp
		make -C obj_dir -f V$*_tb.mk V$*_tb

%_tb.vcd:	obj_dir/V%_tb
		$<

# Run FPGA implementation to the palcement stage to get a utilization report.
%_util:		
		echo "Utilization report for " $*
		vivado -mode tcl -source aes_util.tcl -tclargs $*

clean:		
		-@$(MAKE) -f Makefile.coq clean
		rm -rf _CoqProject Makefile.coq Makefile.coq.conf AESSV
		git clean -Xfd
