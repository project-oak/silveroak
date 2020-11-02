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

.PHONY: all coq clean compile_pinmux

all:		coq pinmux.sv compile_pinmux

VERILATOR = verilator +1800-2012ext+sv verilator.vlt
VLINT = $(VERILATOR) --lint-only

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

PinmuxSV:	coq PinmuxSV.hs
		ghc --make PinmuxSV.hs

pinmux.sv:	coq PinmuxSV
		./PinmuxSV

compile_pinmux:	pinmux.sv
		cd snapshot && $(MAKE)

clean:		
		-@$(MAKE) -f Makefile.coq clean
		rm -rf PinmuxSV.hi PinmuxSV.o PinmuxSV \
		       Pinmux.vo Pinmux.o Pinmux.hs Pinmux.hi pinmux.sv
		rm -rf Makefile.coq Makefile.coq.conf
		cd snapshot && $(MAKE) clean
