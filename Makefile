# See LICENSE for licensing details.

CMDS := src/abella src/abella_doc src/abella_dep
MODE := exe
BINS := $(CMDS:%=%.$(MODE))

.PHONY: all
all: support/.stamp
	dune build $(BINS)

.PHONY: all-release
all-release: # support/.stamp
	dune build --release $(BINS)

support/.stamp: $(wildcard support/ts/*.ts support/css/*.css)
	( cd support && \
	  npm install --no-save && \
	  npm run build && \
	  touch .stamp )

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	$(RM) $(AIN)
	echo 'bin: [' >> $(AIN)
	echo '"_build/default/src/abella.exe" {"abella"}' >> $(AIN)
	echo '"_build/default/src/abella_doc.exe" {"abella_doc"}' >> $(AIN)
	echo '"_build/default/src/abella_dep.exe" {"abella_dep"}' >> $(AIN)
	echo ']' >> $(AIN)
	echo 'man: [' >> $(AIN)
	for pr in _build/default/src/*.exe ; do \
	  $$pr --help=groff > $${pr%%.exe}.1 ; \
	  echo '"'$${pr%%.exe}.1'"' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)
	echo 'share: [' >> $(AIN)
	for f in emacs/* `find examples -type f | grep -E '(sig|mod|thm)$$'` ; do \
	    echo '"'$$f'"' '{"'$$f'"}' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)

.PHONY: clean
clean:
	dune clean
	$(RM) abella $(BINS) $(AIN)

.PHONY: test
test:
	dune runtest --release

.PHONY: publish-doc
publish-doc: examples/make.stamp
	rsync -aviz \
	  --exclude '*.thc' \
	  --exclude '*.out' \
	  --exclude '*.json' \
	  --exclude '*.stamp' \
	  --exclude '.gitignore' \
	  examples abellaweb@abella-prover.org:abella-prover.org/

examples/make.stamp: $(wildcard examples/**/*.{sig,mod,thm})
examples/make.stamp: $(wildcard _build/default/src/abella*.exe)
examples/make.stamp: $(wildcard $(patsubst %.thm,%.thc,$(wildcard examples/**/*.thm)))
examples/make.stamp:
	git clean -fxd examples
	dune exec src/abella_doc.exe -- -r examples
	touch examples/make.stamp
