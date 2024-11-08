default: clear clean fmt build tests proofs exec


clear:
	@clear

clean:
	@dune clean

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
	@cat proofs/k.proof | dune exec ./main.exe
	@echo "\n\n"
	@cat proofs/app.proof | dune exec ./main.exe
	@echo "\n\n"
	@cat proofs/comp.proof | dune exec ./main.exe
	@echo "\n\n"
	@cat proofs/appid.proof | dune exec ./main.exe
	@echo "\n\nSimple - Proofs : Ok\n\n"


.PHONY: proofs
