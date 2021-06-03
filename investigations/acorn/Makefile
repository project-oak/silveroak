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

.PHONY: all clean

CIRCUITS = nandgate addmod pipe2
SV =  $(CIRCUITS:=.sv)

all:	Makefile.coq $(SV) pipe2tb.vcd
	$(MAKE) -f Makefile.coq

pipe2tb.vcd:	pipe2.sv 
		iverilog -g2012 -o pipe2_tb pipe2.sv pipe2_tb.sv && vvp pipe2_tb

%.sv.out:	Acorn.v Makefile.coq
		$(MAKE) -f Makefile.coq

%.sv:	%.sv.out ExtractSystemVerilog
	./ExtractSystemVerilog $*.sv
	iverilog -g2012 -o $* $*.sv
		

Makefile.coq:	
		coq_makefile -f _CoqProject -o Makefile.coq

ExtractSystemVerilog:	ExtractSystemVerilog.hs
			ghc ExtractSystemVerilog.hs


clean:	
		 -$(MAKE) -f Makefile.coq clean
		 rm -rf Makefile.coq ExtractSystemVerilog $(CIRCUITS) $(SV) pipe2_tb *.vcd *.out
