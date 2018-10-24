#

SHELL=bash

# Profiling verbosity for library-test
PROFVERB=7

# Various paths and commands

TOP=.
# mk/path.mk uses TOP, so include after the definition of TOP.
include ./mk/paths.mk

CABAL_CMD=cabal

# Run in interactive and parallel mode by default


PARALLEL_TESTS = $(shell getconf _NPROCESSORS_ONLN)



AGDA_TESTS_OPTIONS ?=-i -j$(PARALLEL_TESTS)


PHONY : default
default: install-bin


# Install Agda using Stack
.PHONY : stack-install-bin
stack-install-bin :
	stack build agda-ocaml:exe:agda-ocaml \
		--flag Agda:enable-cluster-counting \
		--no-haddock \
		--no-library-profiling \
		--stack-yaml stack-lts-12.yaml




.PHONY : stack-install-test
stack-install-test :
	stack build agda-ocaml:test:agda-ocaml-tests \
		--no-run-tests \
		--flag Agda:enable-cluster-counting \
		--no-haddock \
		--no-library-profiling \
		--stack-yaml stack-lts-12.yaml


# Copy the artefacts built by Stack as if they were build by Cabal.
.PHONY : stack-copy-artefacts
stack-copy-artefacts : stack-install-bin stack-install-test
	mkdir -p $(TOP)/build/
	cp -r $(shell stack path --dist-dir)/build $(TOP)


.PHONY : install-bin
install-bin : stack-install-bin stack-install-test stack-copy-artefacts




.PHONY : compiler-test
compiler-test :
	@echo "======================================================================"
	@echo "========================== Compiler tests ============================"
	@echo "======================================================================"
	@AGDA_BIN=$(AGDA_BIN) $(AGDA_TESTS_BIN) $(AGDA_TESTS_OPTIONS) --regex-include all/Compiler





debug :
	@echo "AGDA_BIN           = $(AGDA_BIN)"
	@echo "AGDA_TESTS_BIN     = $(AGDA_TESTS_BIN)"
	@echo "AGDA_TESTS_OPTIONS = $(AGDA_TESTS_OPTIONS)"
	@echo "CABAL_CMD          = $(CABAL_CMD)"
	@echo "PARALLEL_TESTS     = $(PARALLEL_TESTS)"
