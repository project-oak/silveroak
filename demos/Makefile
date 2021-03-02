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

# By default, this Makefile skips building the targets which require Alectryon
# to build webpages for navigable Coq proofs.

# Build Coq proofs:
# make OR make coq

# Build webpages:
# export ALECTRYON_PATH=path/to/alectryon
# make html

# Clean:
# make clean

.PHONY: all coq html

all: coq

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

minimize-requires: coq
	../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:    $(shell find . -name '*.v' | sort)
		@echo "INSTALLDEFAULTROOT = Demos" >> _CoqProject
		@echo "-R ../cava/Cava Cava" >> _CoqProject
		@echo "-R ../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

clean:
		-@$(MAKE) -f Makefile.coq clean
		rm -rf _CoqProject Makefile.coq Makefile.coq.conf dist
		git clean -Xfd

# build demo webpages (requires alectryon -- set $ALECTRYON_PATH variable to local alectryon clone)
html:	coq
	$(ALECTRYON_PATH)/alectryon.py --backend webpage \
	       	-o ../doc/demo/tutorial.html --output-directory ../doc/demo \
	       	-R ../cava/Cava Cava \
		-R ../third_party/coq-ext-lib/theories ExtLib \
		-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil \
		tutorial.v
