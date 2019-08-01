coq:	Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:	Counter.v
		coq_makefile -f _CoqProject -o Makefile.coq

clean:
		$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq Counter.ml Counter.mli

