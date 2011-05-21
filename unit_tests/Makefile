DIRS=$(wildcard *_tests)
DIRS_TEST=$(addsuffix .test,$(DIRS))
DIRS_CLEAN=$(addsuffix .clean,$(DIRS))

SHELL=/bin/bash

test: $(DIRS_TEST)
clean: $(DIRS_CLEAN)

$(DIRS_TEST): %.test: limit
	@echo -n "Testing $* "
	@$(MAKE) -s -C $* test
	@echo

$(DIRS_CLEAN): %.clean:
	$(MAKE) -C $* clean

limit: limit.c
	gcc -o limit limit.c
	chmod u+x limit

.PHONY: test $(DIRS_TEST) clean $(DIRS_CLEAN)
.SILENT: test
