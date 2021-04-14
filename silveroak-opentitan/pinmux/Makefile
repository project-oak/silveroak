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

.PHONY: all coq minimize-requires clean compile_pinmux _CoqProject

all:		coq pinmux.sv compile_pinmux

VERILATOR = verilator +1800-2012ext+sv verilator.vlt
VLINT = $(VERILATOR) --lint-only

_CoqProject:    $(shell find . -name '*.v' | sort)
		@echo "INSTALLDEFAULTROOT = Pinmux" > _CoqProject
		@echo "-R . Pinmux" >> _CoqProject
		@echo "-R ../../cava/Cava Cava" >> _CoqProject
		@echo "-R ../../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

minimize-requires: coq
	../../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

PinmuxSV:	coq PinmuxSV.hs
		cabal build pinmux

pinmux.sv:	coq PinmuxSV
		cabal run pinmux

compile_pinmux:	pinmux.sv
		cd snapshot && $(MAKE)

clean:
		-@$(MAKE) -f Makefile.coq clean
		rm -rf PinmuxSV.hi PinmuxSV.o PinmuxSV \
		       Pinmux.vo Pinmux.o Pinmux.hs Pinmux.hi pinmux.sv
		rm -rf _CoqProject Makefile.coq Makefile.coq.conf
		cd snapshot && $(MAKE) clean
