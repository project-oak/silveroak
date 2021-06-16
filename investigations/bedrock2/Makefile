#
# Copyright 2021 The Project Oak Authors
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

.PHONY: all coq clean aes.c

all:		coq

_CoqProject:    $(shell find . -name '*.v' | sort)
		@echo "INSTALLDEFAULTROOT = Bedrock2Experiments" > _CoqProject
		@echo "-R . Bedrock2Experiments" >> _CoqProject
		@echo "-R ../../cava/Cava Cava" >> _CoqProject
		@echo "-R ../../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../../third_party/bedrock2/bedrock2/src/bedrock2 bedrock2" >> _CoqProject
		@echo "-R ../../third_party/bedrock2/compiler/src/compiler compiler" >> _CoqProject
		@echo "-R ../../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@echo "-R ../../third_party/bedrock2/deps/riscv-coq/src/riscv riscv" >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

clean:
	-@$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq
	rm -f aes.c aes.c.out uart.c uart.c.out
