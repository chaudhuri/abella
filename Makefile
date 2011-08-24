OCB = ocamlbuild -use-ocamlfind -classic-display

.PHONY: all
all: src/version.ml src/abella.ml src/abella.native src/abella.cma
	${RM} src/abella.ml

%.native:
	${OCB} $@

%.cma:
	${OCB} $@

src/version.ml:
	if test ! -e $@ ; then \
	  echo 'let version = "$(VERSION)"' > $@ ; \
	fi

src/abella.ml: src/main.ml
	cp $< $@

clean:
	${OCB} -clean
