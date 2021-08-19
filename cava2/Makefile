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

.PHONY: all clean coq _CoqProject

all:	Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:    $(shell find . -name '*.v' | sort)
		@echo "INSTALLDEFAULTROOT = Cava" > _CoqProject
		@echo "-R . Cava" >> _CoqProject
		@echo "-R ../cava/Cava Cava" >> _CoqProject
		@echo "-R ../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@echo "-R ../silveroak-opentitan/hmac/Spec HmacSpec" >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

coq: Makefile.coq
		$(MAKE) -f Makefile.coq

clean: _CoqProject
		 -$(MAKE) -f Makefile.coq clean
		 rm -rf Makefile.coq
