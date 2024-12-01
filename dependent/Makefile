default: clear clean fmt build tests proofs exec


clear:
	@clear

clean:
	@dune clean
	@rm -rf tmp

fmt:
	@dune fmt

build:
	@dune build

tests:
	@dune exec -- ./main.exe --tests

exec:
	@dune exec ./main.exe

proofs: clear
	@echo "\n\nTesting proofs :\n\n"
	@for file in proofs/*.proof; do \
		echo "--------------------------------------"; \
		echo "Proof in $$file\n"; \
		cat "$$file" | dune exec ./main.exe; \
		echo "--------------------------------------\n\n"; \
	done
	@echo "\n\nDependent - Proofs : Ok\n\n"


.PHONY: proofs
