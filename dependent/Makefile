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

proofs:
	@echo "\n\nTesting proofs :\n\n"
	@echo "TODO"
	@echo "\n\nDependent - Proofs : Ok\n\n"


.PHONY: proofs
