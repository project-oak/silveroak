#
# Copyright 2019 The Project Oak Authors
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

all:		nand2.vhd onebitadder.vhd vhdl_compile

Makefile.coq:
		coq_makefile -f _CoqProject -o Makefile.coq

Nand2VHDL:	Makefile.coq Cava2VHDL.hs Nand2VHDL.hs
		$(MAKE) -f Makefile.coq
		ghc -W --make Nand2VHDL.hs

nand2.vhd:	Nand2VHDL
		./Nand2VHDL


OneBitAdder2VHDL:	Makefile.coq Cava2VHDL.hs OneBitAdder.hs
			$(MAKE) -f Makefile.coq
			ghc --make OneBitAdder2VHDL.hs

onebitadder.vhd:	OneBitAdder2VHDL
			./OneBitAdder2VHDL

vhdl_compile:
		xvhdl nand2.vhd
		xvhdl nand2_tb.vhd
		xvhdl onebitadder.vhd

clean:
		rm -rf  *.v.d *.vo *.o *.hi .*.aux *.glob \
		        xsim.dir xvhdl.pb xvhdl.log Makefile.coq.conf
		xargs rm -rf < .gitignore

.PHONY: clean vhdl_compile
