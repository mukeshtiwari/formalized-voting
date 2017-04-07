Run the following on terminal.

> make extractlib

It will generated Haskell library Lib.hs for counting. Go to line 439 in Lib.hs, replace 
"type Cand = ()" by "data Cand = A | B | C | D" and 
"cand_all :: List Cand
cand_all =
  Prelude.error "AXIOM TO BE REALIZED"" by 
"cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D Nil)))"

Now run 
> make runmain
>./Main
If you want to re-run the program then run 
> make cleanlib
> make cleanmain
