FILES=proof.v

proof.v:
	coqc proof.v
documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	-rm -f doc/html/*.html
	coqc -dump-glob ALL.glob $(FILES)
	doc/coq2html -o 'doc/html/%.html' ALL.glob $(FILES)
	cp doc/coq2html.css doc/coq2html.js doc/html/
