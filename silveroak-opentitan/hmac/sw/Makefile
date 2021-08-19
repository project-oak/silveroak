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

_CoqProject:    $(shell find . -name '*.v' | sort)
		@echo "INSTALLDEFAULTROOT = HmacSoftware" > _CoqProject
		@echo "-R . HmacSoftware" >> _CoqProject
		@echo "-R ../Spec HmacSpec" >> _CoqProject
		@echo "-R ../../../firmware Bedrock2Experiments" >> _CoqProject
		@echo "-R ../../../cava/Cava Cava" >> _CoqProject
		@echo "-R ../../../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../../../third_party/bedrock2/bedrock2/src/bedrock2 bedrock2" >> _CoqProject
		@echo "-R ../../../third_party/bedrock2/compiler/src/compiler compiler" >> _CoqProject
		@echo "-R ../../../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@echo "-R ../../../third_party/bedrock2/deps/riscv-coq/src/riscv riscv" >> _CoqProject
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