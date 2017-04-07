Run the following on terminal.
>make -f Makefile
It will generated Haskell library for counting. Go to line 439,replace 
type Cand = () with data Cand = A | B | C | D 
and replace 
cand_all :: List Cand
cand_all =
  Prelude.error "AXIOM TO BE REALIZED"

with 
cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D Nil)))

