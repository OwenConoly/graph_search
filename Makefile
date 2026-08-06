.PHONY: all coqutil clean

all: coqutil Makefile.coq
	$(MAKE) -f Makefile.coq

coqutil:
	$(MAKE) -C coqutil

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
