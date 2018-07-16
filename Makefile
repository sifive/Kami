VS:=$(shell find . -type f -name '*.v')

.PHONY: coq clean

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq.all

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	rm -rf *.v.d *.glob *.vo *~ *.hi *.o
	rm -f Makefile.coq.all

