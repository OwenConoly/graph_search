.DEFAULT_GOAL := graph_search

.PHONY: clean all coqutil graph_search

COQC ?= "$(COQBIN)coqc"

coqutil:
	$(MAKE) -C coqutil notest

graph_search: coqutil Makefile.coq
	$(MAKE) -f Makefile.coq

all: graph_search

COQ_MAKEFILE := $(COQBIN)coq_makefile -docroot graph_search $(COQMF_ARGS)

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -C coqutil clean
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf
