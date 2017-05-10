%.vo : %.v
	coqc $*.v

ListLemma.vo : ListLemma.v

SchulzeSynthesis.vo : ListLemma.vo SchulzeSynthesis.v

Extraction.vo : SchulzeSynthesis.vo Extraction.v

ExtractionNative.vo : SchulzeSynthesis.vo ExtractionNative.v

lib.ml : Extraction.vo

lib.mli : lib.ml

bench: Main rand.pl
	@for i in 100 1000 10000 100000; do \
    echo -n "Counting $$i ballots ..\n  "; \
    ./rand.pl $$i | time -f %E ./main.native > /dev/null; \
  done


clean:
	rm -rf _build *.vo *.glob lib.ml lib.mli main.native  2>/dev/null || true

Main : lib.ml lib.mli derivation.ml main.ml
	ocamlbuild -use-ocamlfind -r -package ppx_deriving.std   -use-menhir  main.native	


