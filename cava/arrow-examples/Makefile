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

.PHONY: all coq auto_vcds clean

all:		coq xorArrow.vcd loopedNandArrow.vcd

VERILATOR = verilator +1800-2012ext+sv verilator.vlt
VLINT = $(VERILATOR) --lint-only

Makefile.coq:
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

ArrowExamplesSV:	ArrowExamplesSV.hs
			ghc --make $^

xorArrow.sv:	coq ArrowExamplesSV
		./ArrowExamplesSV
		$(VLINT) xorArrow.sv
		$(VLINT) loopedNandArrow.sv


loopedNandArrow.sv:	xorArrow.sv

xorArrow.vcd:	xorArrow.sv testbench/xorArrow_tb.sv
		iverilog -g2012 -o xorArrow.vvp $^
		./xorArrow.vvp

loopedNandArrow.vcd:	loopedNandArrow.sv testbench/loopedNandArrow_tb.sv
		iverilog -g2012 -o loopedNandArrow.vvp $^
		./loopedNandArrow.vvp

clean:
		-@$(MAKE) -f Makefile.coq clean
		git clean -xfd
