VERSION = 1.4.0-forallp

OCB = ocamlbuild -use-ocamlfind -classic-display -no-links

.PHONY: all
all: vstamp src/abella.ml src/abella.native src/abella.cma
	${RM} src/abella.ml
	ln -sf _build/src/abella.native abella

%.native:
	${OCB} $@

%.cma:
	${OCB} $@

.PHONY: vstamp
vstamp:
	echo 'let version = "$(VERSION)"' > src/version.ml

src/abella.ml: src/main.ml
	cp $< $@

clean:
	${OCB} -clean
