all: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: all clean

Makefile.coq: _CoqProject
	coq_makefile -o Makefile.coq -f _CoqProject
