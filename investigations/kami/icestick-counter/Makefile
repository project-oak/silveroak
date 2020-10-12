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

OCB = ocamlbuild
KAMI = ../../../../kami

all: counter5_top.bin

Counter.ml:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Counter.v
		coq_makefile -f _CoqProject -o Makefile.coq

clean:
		-$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq Counter.ml Counter.mli Counter5.bsv *.bo \
		       mkModule1.v counter5_tb.vcd obj_dir Makefile.coq.bak \
		       PP.ml .Counter* \
		       counter5_top.json counter5_top.asc counter5_top.bin \
		       obj counter5_top.json  counter5_top.asc counter5_top.json \
		       mkModule1 mkModule1.xml non-layout.eps tables.txt
		$(OCB) -clean

PP.ml:		$(KAMI)/Kami/Ext/Ocaml/PP.ml
		cp $< .
		ex -sc '%s/Target/Counter/|x' $@

Main.native:	Counter.ml PP.ml
		$(OCB) Main.native Counter.v 

Counter5.bsv:	Main.native
		./$< $@
		ex -sc '/RegFileZero/d|x' $@
		ex -sc '/MulDiv/d|x' $@

mkModule1.v:	Counter5.bsv
		$(HPRLS)/bsvc/priv_distro/bin/bsvc -incdir=$(HPRLS)/bsvc/priv_distro/libs/camlib Counter5.bsv -g mkModule1 -vnl=mkModule1.v -conerefine=disable

counter5_top.json:	mkModule1.v counter5_top.v
			yosys -p 'synth_ice40 -top counter5_top -json counter5_top.json' mkModule1.v counter5_top.v 

counter5_top.asc:	counter5_top.json
			nextpnr-ice40 --hx1k --json counter5_top.json --pcf counter5_top.pcf --asc counter5_top.asc 


counter5_top.bin:	counter5_top.asc
			icepack counter5_top.asc counter5_top.bin

configure:		counter5_top.bin
			iceprog $<

.PHONY: all clean configure

