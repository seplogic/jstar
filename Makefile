# configurations

ifndef CORESTAR_HOME
	CORESTAR_HOME=$(CURDIR)/../corestar
endif
export CORESTAR_HOME

ifndef JSTAR_HOME
	JSTAR_HOME=$(CURDIR)
endif
export JSTAR_HOME

SRC_DIRS=src corestar_src
MAINS=jstar
OB_FLAGS=-cflags -annot -yaccflags -v -use-ocamlfind

# section with stuff that shouldn't change often

SHELL=/bin/bash
SRC_SUBDIRS=$(addsuffix .subdirs,$(SRC_DIRS))
OCAMLBUILD=ocamlbuild $(OB_FLAGS) `cat $(SRC_SUBDIRS)`
CPLN=corestar_scripts/_build/cpln.byte

build: native

native byte: $(SRC_SUBDIRS) corestar_scripts
	@$(MAKE) -C corestar_scripts byte
	@$(OCAMLBUILD) $(addsuffix .$@,$(MAINS))
	@mkdir -p bin
	@for f in $(MAINS); do $(CPLN) $$f.$@ bin/$$f; rm $$f.$@; done

test: test-native

test-native test-byte: test-%: %
	$(MAKE) -s -C unit_tests

doc:
	$(MAKE) -C doc/tutorial # DEV

all: build test

clean:
	ocamlbuild -clean
	rm -f *.subdirs
	rm -rf bin
	rm -rf corestar_src corestar_scripts # DEV
	$(MAKE) -C unit_tests clean
	$(MAKE) -C doc/tutorial clean # DEV

%.subdirs: %
	@ls -F $*/ | grep / | sed "s./.." | sed "s.^.-I $*/." > $*.subdirs

corestar_src:
	ln -sf "$(CORESTAR_HOME)/src" corestar_src

corestar_scripts:
	ln -sf "$(CORESTAR_HOME)/scripts" corestar_scripts

.PHONY: build byte clean doc native test

-include .install.mk

#vim:noet:
