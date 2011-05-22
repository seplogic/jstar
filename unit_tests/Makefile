DIRS=$(wildcard *_tests)
DIRS_TEST=$(addsuffix .test,$(DIRS))
DIRS_CLEAN=$(addsuffix .clean,$(DIRS))

SHELL=/bin/bash

test: $(DIRS_TEST)
clean: $(DIRS_CLEAN)
	rm -f limit

$(DIRS_TEST): %.test: limit
	@echo -n "Testing $* "
	@$(MAKE) -s -C $* test
	@echo

$(DIRS_CLEAN): %.clean:
	$(MAKE) -C $* clean

limit: limit.c
	gcc -O2 -o limit limit.c

.PHONY: test $(DIRS_TEST) clean $(DIRS_CLEAN)
.SILENT: test
