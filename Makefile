VS:=$(wildcard *.v)
VS += $(wildcard Lib/*.v)
VS += $(wildcard Compile/*.v)

.PHONY: coq src clean

ARGS := -R . Kami -R ../bbv bbv

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(VS) -o Makefile.coq.all

src: Makefile.coq.src
	$(MAKE) -f Makefile.coq.src

Makefile.coq.src: Makefile $(VS)
	$(COQBIN)coq_makefile $(ARGS) $(VS) -o Makefile.coq.src

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
	rm -f Makefile.coq.src
