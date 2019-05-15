INSTALL_ARGS := $(if $(PREFIX),--prefix $(PREFIX),)

build:
	time -p dune build @install --profile release

install: build
	dune install $(INSTALL_ARGS)

uninstall:
	dune uninstall $(INSTALL_ARGS)

reinstall: uninstall install

clean:
	dune clean

doc:
	dune build @doc

test:
	dune runtest --profile release

updatetest:
	dune runtest --auto-promote

all: build test doc

utop: install
	utop-full -short-paths -init ocamlinit

hybrid_demo:
	dune exec frenetic edge hybrid\
		examples/topo.json\
		examples/real_network.json\
		examples/edge_program.json\
		--profile release; \
	cat hybrid.json

.PHONY: build install uninstall reinstall clean doc test all utop updatetest
