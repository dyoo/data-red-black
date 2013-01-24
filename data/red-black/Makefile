doc:
	scribble  ++xref-in setup/xref load-collections-xref --redirect-main http://docs.racket-lang.org/   --dest-name index.html manual.scrbl

	scribble  ++xref-in setup/xref load-collections-xref --redirect-main http://docs.racket-lang.org/   --dest-name augmented.html augmented.scrbl
	scribble  ++xref-in setup/xref load-collections-xref --redirect-main http://docs.racket-lang.org/   --dest-name ordered-set.html ordered-set.scrbl
	scribble  ++xref-in setup/xref load-collections-xref --redirect-main http://docs.racket-lang.org/   --dest-name positional.html positional.scrbl

web:
	scp -r * hashcollision.org:webapps/htdocs/red-black/
