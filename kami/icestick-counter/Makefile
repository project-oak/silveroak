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

OCB = ocamlbuild -use-ocamlfind
KAMI = ../../../kami

all: counter4_tb.vcd counter4.bit

Counter.ml:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Counter.v
		coq_makefile -f _CoqProject -o Makefile.coq

clean:		clean_vivado
		-$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq Counter.ml Counter.mli Counter4.bsv *.bo \
		       mkModule1.v counter4_tb.vcd obj_dir Makefile.coq.bak \
		       PP.ml RegFileZero.bsv MulDiv.bsv .Counter* \
			   counter4_top.json counter4_top.asc counter4_top.bin
		$(OCB) -clean

PP.ml:		$(KAMI)/Kami/Ext/Ocaml/PP.ml
		cp $< .
		sed -i 's/Target/Counter/' $@

Main.native:	Counter.ml PP.ml
		$(OCB) Main.native Counter.v 

Counter4.bsv:	Main.native
		./$< $@

RegFileZero.bo:	$(KAMI)/Kami/Ext/BluespecFrontEnd/sim/RegFileZero.bsv
		cp $< .
		bsc RegFileZero.bsv


MulDiv.bo:	$(KAMI)/Kami/Ext/BluespecFrontEnd/sim/MulDiv.bsv
		cp $< .
		bsc MulDiv.bsv

mkModule1.v:	Counter4.bsv RegFileZero.bo MulDiv.bo
		bsc -verilog -g mkModule1 $<

counter4_tb.vcd:	mkModule1.v
			verilator --cc --trace mkModule1.v --exe counter4_tb.cpp
			make -C obj_dir -f VmkModule1.mk VmkModule1
			obj_dir/VmkModule1

counter4_top.json:	mkModule1.v counter4_top.v
				yosys -p 'synth_ice40 -top counter4_top -json counter4_top.json' mkModule1.v counter4_top.v 

counter4_top.asc:	counter4_top.json
					nextpnr-ice40 --hx1k --json counter4_top.json --pcf counter4_top.pcf --asc counter4_top.asc 


counter4_top.bin:	counter4_top.asc
					icepack counter4_top.asc counter4_top.bin

.PHONY: all clean configure

