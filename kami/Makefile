OCB = ocamlbuild -use-ocamlfind
KAMI = ../../kami

all: counter4_tb.vcd

Counter.ml:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Counter.v
		coq_makefile -f _CoqProject -o Makefile.coq

clean:
		-$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq Counter.ml Counter.mli Counter4.bsv *.bo \
		       mkModule1.v counter4_tb.vcd obj_dir
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

.PHONY: all clean

