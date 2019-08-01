coq:	Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:	Counter.v
		coq_makefile -R ../../kami/Kami Kami Counter.v -o Makefile.coq

clean:
		$(MAKE) -f Makefile.coq clean
		rm -rf Makefile.coq

