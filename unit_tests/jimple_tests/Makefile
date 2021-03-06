SHELL=/bin/bash

ifndef TARGETS
  TARGETS =
endif

ifndef CLEAN
  CLEAN =  *.class *~ *.dot *proof_file*.txt \#* .\#* *.core
endif 

ifndef SOURCES
  SOURCES =  $(addsuffix .java, $(TARGETS)) 
endif

ifndef SUBDIRSDEF
   SUBDIRSDEF = foo
   SUBDIRS = popl2008 pool visitor traditional multinh linkedlist subject
endif

ifndef DIR
   DIR = 
endif 

ifdef DIR
  INDENT := $(INDENT) " "
endif

export INDENT 

all: $(addsuffix .jimple, $(TARGETS)) 
	@for dir in ${SUBDIRS} ; do $(MAKE) -C $$dir all; done

test: all $(addsuffix .test, $(TARGETS)) $(addsuffix .test.dir, ${SUBDIRS})

time :  all $(addsuffix .time, $(TARGETS))
	@for dir in ${SUBDIRS} ; do $(MAKE) -C $$dir time ; done

%.class: $(SOURCES)
	javac -g $?  || (echo "WARNING: Javac failed, using old class file" ; touch $@)

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number  || (echo "WARNING: Soot failed, using old Jimple file." ; touch $@)

%.test.dir: 
	@$(MAKE) -C $* test

clean:: 
	for dir in ${SUBDIRS} ; do $(MAKE) -C $$dir clean; done
	@rm -f $(CLEAN)

%.time:
	@echo $(INDENT) Timing $(DIR)/$*
	@time ./runtest $*.jimple >/dev/null

%.test : %.jimple
	@"${JSTAR_HOME}/unit_tests/jimple_tests/test.sh" "${JSTAR_HOME}" "$*"

.PHONY: test clean

