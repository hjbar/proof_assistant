default: clear clean fmt build


clear:
	@clear

clean fmt build tests proofs exec:
	@echo "--------------------------\n"
	@echo "Simple :\n"
	@$(MAKE) -C simple $@
	@echo "--------------------------\n"
	@echo "Dependent :\n"
	@$(MAKE) -C dependent $@
	@echo "--------------------------\n"


.PHONY: proofs
