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

# By default, this Makefile skips building the targets which require Alectryon
# to build webpages for navigable Coq proofs.

# Build Coq proofs:
# make OR make coq

# Build webpages:
# export ALECTRYON_PATH=path/to/alectryon
# make html

# Clean:
# make clean

.PHONY: all coq miminize-requires clean html

SV = sum8.sv

BENCHES = $(SV:.sv=_tb.sv)
CPPS = $(SV:.sv=_tb.cpp)
VCDS = $(SV:.sv=_tb.vcd)

.PRECIOUS: $(VCDS)

all: coq $(VCDS)

VERILATOR = verilator +1800-2012ext+sv verilator.vlt

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq >/dev/null # don't show the printed output; the tutorial has long print statements

minimize-requires: coq
	../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:    $(shell find . -name '*.v' | sort)
		rm -f _CoqProject
		@echo "INSTALLDEFAULTROOT = Demos" >> _CoqProject
		@echo "-R ../cava/Cava Cava" >> _CoqProject
		@echo "-R ../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		@printf '%s\n' $^ >> _CoqProject

TutorialSV:	coq TutorialSV.hs
		ghc --make TutorialSV.hs
		./TutorialSV

$(SV) $(BENCHES) $(CPPS):	coq TutorialSV

obj_dir/V%_tb:	%.sv %_tb.sv %_tb.cpp
		$(VERILATOR) --trace --cc --top-module $*_tb $*_tb.sv $*.sv --exe $*_tb.cpp
		make -C obj_dir -f V$*_tb.mk V$*_tb

%_tb.vcd:	obj_dir/V%_tb
		$<


clean:
		-@$(MAKE) -f Makefile.coq clean
		rm -rf _CoqProject Makefile.coq Makefile.coq.conf dist
		git clean -Xfd

# build demo webpages (requires alectryon -- set $ALECTRYON_PATH variable to local alectryon clone)
html:
	$(ALECTRYON_PATH)/alectryon.py --backend webpage --webpage-style floating \
	       	-o ../docs/demo/tutorial.html --output-directory ../docs/demo \
	       	-R ../cava/Cava Cava \
		-R ../third_party/coq-ext-lib/theories ExtLib \
		-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil \
		tutorial.v
