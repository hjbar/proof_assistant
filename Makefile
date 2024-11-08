default: simple dependent

simple:
	$(MAKE) -C simple exec

dependent:
	$(MAKE) -C dependent exec

.PHONY: default simple dependent
