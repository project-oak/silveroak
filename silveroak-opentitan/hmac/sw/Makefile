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

.PHONY:	all coq minimize-requires clean _CoqProject

all:		coq

# Note: make does not interpret "\n", and this is intended (printf will interpret them)
DEPS_NL=-R . HmacSoftware
DEPS_NL+=\n-R ../Spec HmacSpec
DEPS_NL+=\n-R ../../../firmware Bedrock2Experiments
DEPS_NL+=\n-R ../../../cava/Cava Cava
DEPS_NL+=\n-R ../../../third_party/coq-ext-lib/theories ExtLib
DEPS_NL+=\n-R ../../../third_party/bedrock2/bedrock2/src/bedrock2 bedrock2
DEPS_NL+=\n-R ../../../third_party/bedrock2/compiler/src/compiler compiler
DEPS_NL+=\n-R ../../../third_party/bedrock2/deps/coqutil/src/coqutil coqutil
DEPS_NL+=\n-R ../../../third_party/bedrock2/deps/riscv-coq/src/riscv riscv

DEPS=$(subst \n, ,$(DEPS_NL))

_CoqProject:    $(shell find . -name '*.v' -and -not -name '*_HexOutput.v' | sort)
		@echo "INSTALLDEFAULTROOT = HmacSoftware" > _CoqProject
		@printf -- '$(DEPS_NL)\n' >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

minimize-requires: coq
	../../../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

clean:
	-@$(MAKE) -f Makefile.coq clean
	rm -rf _CoqProject Makefile.coq Makefile.coq.conf

.PRECIOUS: %.vo %.o %.hex %.s %.bin

COQC?=coqc
COQC_OPTIONS=$(DEPS)

TOOLCHAIN_BIN?=/tools/riscv/bin/
CROSS_COMPILE?=$(TOOLCHAIN_BIN)riscv32-unknown-elf-
RISCV_AR?=$(CROSS_COMPILE)ar
RISCV_LD?=$(CROSS_COMPILE)ld

%.hex: %_HexOutput.v coq
	$(COQC) $(COQC_OPTIONS) $< > $@

%.bin: %.hex
	xxd -r -p < $< > $@

# Turn a binary (-b binary) file into a relocatable (-r) object file
# with symbol (--defsym) named the same as the file but without extension ($*),
# referencing the start of the file (.)
%.o: %.bin
	$(RISCV_LD) -r -b binary --defsym $*=. -o $@ $<

# Turn an object file into an archive file ("library") because that's what the meson build system looks for
%.a: %.o
	$(RISCV_AR) rs $@ $<
