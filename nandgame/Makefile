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

.PHONY: all compile clean

all:		compile inverter.sv

Makefile.coq:
		coq_makefile -f _CoqProject -o Makefile.coq

compile:	Makefile.coq
		$(MAKE) -f Makefile.coq

NandGameSV:	NandGameSV.hs
		ghc --make NandGameSV.hs

inverter.sv:	compile NandGameSV
		./NandGameSV

clean:
		rm -rf  *.v.d *.vo *.o *.hi .*.aux *.glob \
		        xsim.dir xvhdl.pb xvhdl.log Makefile.coq Makefile.coq.conf \
			FixupAscii NandGateSV \
			inverter.sv andgate.sv fulladder.sv halfadder.sv orgate.sv xorgate.sv

		xargs rm -rf < .gitignore

