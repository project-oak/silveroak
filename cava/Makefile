Nand2.hs:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Cava.v
		coq_makefile Cava.v -o Makefile.coq

clean:	
		rm -rf Nand2.hs Makefile.coq *.v.d *.vo

.PHONY: clean
