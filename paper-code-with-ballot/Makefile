extractlib : Lib.hs

Lib.hs : Extraction.vo
	@coqc Extraction.v

Extraction.vo : SchulzeSynthesis.vo
	@coqc SchulzeSynthesis.v

SchulzeSynthesis.vo : ListLemma.v
	@coqc ListLemma.v


cleanlib:
	@rm Lib.hs *.vo *.glob 2>/dev/null


runmain : Main

Main : Lib.hs Derivation.hs Main.hs
	ghc -O2 Main.hs

cleanmain : 
	@rm -rf *.hi *.o Main 2>/dev/null
