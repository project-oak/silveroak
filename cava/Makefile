all:		Nand2VHDL

Makefile.coq:	Cava.v Nand2.v Extract.v
		coq_makefile Cava.v Nand2.v Extract.v -o Makefile.coq

Nand2VHDL:	Makefile.coq
		$(MAKE) -f Makefile.coq
		ghc --make Nand2VHDL.hs

clean:	
		rm -rf  Ascii.hs Cava.hs Nand2.hs Makefile.coq *.v.d *.vo *.o *.hi Makefile.coq.conf *.glob \
			Basics.* BinNat.* BinNums.* BinPos.* Bool.* Datatypes.* Decimal.* \
			List.* Logic.* Nat.* Specif.* String.* Nand2VHDL

.PHONY: clean
