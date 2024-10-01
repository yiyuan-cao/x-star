.PHONY: all build test clean

all: build test

build:
	dune build

test: build
	cram tests/tests.t

clean:
	dune clean