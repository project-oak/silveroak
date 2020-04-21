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

all:		coq auto_vcds

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
		$(VLINT) nandArrow.sv
		$(VLINT) xorArrow.sv
		$(VLINT) feedbackNandArrow.sv

%.vcd:		%.sv testbench/%_tb.sv
		iverilog -g2012 -o $*.vvp $^
		./$*.vvp

.PRECIOUS:	xorArrow.sv feedbackNandArrow.sv

auto_vcds:	xorArrow.vcd feedbackNandArrow.vcd

clean:
		-@$(MAKE) -f Makefile.coq clean
		git clean -xfd
		rm -rf obj_dir
