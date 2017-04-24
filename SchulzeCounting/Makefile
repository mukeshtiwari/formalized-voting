# GHCFLAGS= -prof -fprof-auto
GHCFLAGS = -O2

%.vo : %.v
	coqc $*.v

ListLemma.vo : ListLemma.v

SchulzeSynthesis.vo : ListLemma.vo SchulzeSynthesis.v

Extraction.vo : SchulzeSynthesis.vo Extraction.v

ExtractionNative.vo : SchulzeSynthesis.vo ExtractionNative.v

Lib.hs : Extraction.vo

LibNative.hs : ExtractionNative.vo

bench: Main rand.pl
	@for i in 100 1000 10000 100000; do \
    echo -n "Counting $$i ballots ..\n  "; \
    ./rand.pl $$i | time -f %E ./Main > /dev/null; \
  done

benchnative: MainNative rand.pl
	@for i in 1000 10000 100000 1000000; do \
    echo -n "Counting $$i ballots ..\n  "; \
    ./rand.pl $$i | time -f %E ./MainNative > /dev/null; \
  done

clean:
	rm *.vo *.glob Lib.hs LibNative.hs *.o *.hi *.prof Main MainNative 2>/dev/null || true

Main : Lib.hs Derivation.hs Main.hs
	ghc $(GHCFLAGS)  Main.hs

MainNative : LibNative.hs DerivationNative.hs MainNative.hs
	ghc $(GHCFLAGS)  MainNative.hs

