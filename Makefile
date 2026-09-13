# Thin wrapper around the Rocq-generated makefile (coq-community pattern).
# `make` builds everything listed in _CoqProject; `make gate` runs the
# checks CI runs. The generated file is called CoqMakefile because the
# LLM4Rocq `rocq` plugin (/rocq:checkpoint) invokes `make -f CoqMakefile`.

KNOWNTARGETS := CoqMakefile clean layers admitted axioms gate docs
KNOWNFILES   := Makefile _CoqProject
.DEFAULT_GOAL := invoke-coqmakefile

# Rocq >= 9 ships `rocq makefile`; older installs only have coq_makefile.
ROCQ_MAKEFILE := $(shell command -v rocq >/dev/null 2>&1 && echo "rocq makefile" || echo "coq_makefile")

CoqMakefile: Makefile _CoqProject
	$(ROCQ_MAKEFILE) -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile clean layers admitted axioms gate docs $(KNOWNFILES)

clean:
	-$(MAKE) --no-print-directory -f CoqMakefile cleanall 2>/dev/null
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d

# --- gates -------------------------------------------------------------
layers:
	python3 scripts/check_layers.py

admitted:
	@python3 scripts/check_admitted.py

axioms: invoke-coqmakefile
	./verify.sh --no-clean

gate: layers invoke-coqmakefile admitted axioms

# --- documentation -----------------------------------------------------
# Same coqdoc output as CI: `gallinahtml` lists statements without proof
# scripts, and index.html is the table of contents (the A-Z index of
# identifiers is indexpage.html, see CoqMakefile.local).
docs: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile gallinahtml
	cp html/toc.html html/index.html

# Forward any other target (html, install, theories/foo.vo, ...) to CoqMakefile.
%: invoke-coqmakefile
	@true
