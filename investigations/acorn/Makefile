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

CIRCUITS = nandgate addmod pipe2 delay1 counter6 counter6by4 nestedloop
SV =  $(CIRCUITS:=.sv)

all:	Makefile.coq $(SV) pipe2_tb.vcd delay1_tb.vcd counter6_tb.vcd counter6by4_tb.vcd \
        nestedloop_tb.vcd
	$(MAKE) -f Makefile.coq

%_tb.vcd:	%.sv 
		iverilog -g2012 -o $*_tb $*.sv $*_tb.sv && vvp $*_tb

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
