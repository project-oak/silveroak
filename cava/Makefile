all:		Nand2Alt.hs Cava2VHDL.hi

Nand2Alt.hs:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Cava.v
		coq_makefile Cava.v Nand2.v Extract.v -o Makefile.coq

Cava.hs:	Nand2Alt.hs

Cava2VHDL.hi:	Cava2VHDL.hs Cava.hs
		ghc --make Cava2VHDL.hs

clean:	
		rm -rf Nand2Alt.hs Makefile.coq *.v.d *.vo

.PHONY: clean
