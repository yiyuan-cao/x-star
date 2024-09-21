export HOLLIGHT_DIR=$(shell pwd)/hol-light
export HOLLIGHT_USE_MODULE=1

OCAMLPATH := $(shell ocamlc -where)
CFLAGS = -I$(OCAMLPATH) -fpic

all: libhol_native.a compile_flags.txt

libhol_native.a: caml.o host.o runtime.o
	$(AR) rcs libhol_native.a $^

hol-light/hol_loader.cmo:
	cd hol-light && make

runtime.o: eval.ml hol-light/hol_loader.cmo
	ocamlfind ocamlc -linkall -output-complete-obj -linkpkg -o runtime.o \
		-package compiler-libs.toplevel -package zarith -package camlp-streams \
		-cclib -L/usr/lib eval.ml hol-light/bignum.cmo hol-light/hol_loader.cmo

compile_flags.txt:
	echo $(CFLAGS) > compile_flags.txt

clean:
	cd hol-light && make clean
	rm -f *.o *.so *.cmi *.cmo *.a

.PHONY: all clean
