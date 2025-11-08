# Simple Makefile for SAPSE-Coq (Coq 8.19)
COQPROJECT=_CoqProject
COQMAKEFILE=Makefile.coq

all: coq

$(COQMAKEFILE): $(COQPROJECT)
	@coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

coq: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) -j

clean:
	@[ -f $(COQMAKEFILE) ] && $(MAKE) -f $(COQMAKEFILE) clean || true
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all coq clean
