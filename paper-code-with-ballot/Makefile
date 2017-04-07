all : Lib.hs

#Main : Lib.hs Derivation.hs Main.hs
#	ghc -O2 Main.hs

Lib.hs : Extraction.vo
	@coqc Extraction.v

Extraction.vo : SchulzeSynthesis.vo
	@coqc SchulzeSynthesis.v

SchulzeSynthesis.vo : ListLemma.v
	@coqc ListLemma.v


clean:
	@rm Lib.hs *.vo *.glob 2>/dev/null

