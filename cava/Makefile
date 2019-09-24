all:		Nand2.hs Nand2VHDL

Nand2.hs:	Makefile.coq
		$(MAKE) -f Makefile.coq

Makefile.coq:	Cava.v
		coq_makefile Cava.v Nand2.v Extract.v -o Makefile.coq

Cava.hs:	Nand2.hs

Cava2VHDL.hi:	Cava2VHDL.hs Cava.hs
		ghc --make Cava2VHDL.hs

Nand2VHDL:	Nand2.hs Nand2VHDL.hs
		ghc --make Nand2VHDL.hs

clean:	
		rm -rf  Ascii.hs Cava.hs Nand2.hs Makefile.coq *.v.d *.vo *.o *.hi Makefile.coq.conf *.glob \
			Basics.* BinNat.* BinNums.* BinPos.* Bool.* Datatypes.* Decimal.* \
			List.* Logic.* Nat.* Specif.* String.*

.PHONY: clean
