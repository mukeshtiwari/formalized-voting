Run the following on terminal.
> make extractlib
It will generated Haskell library for counting. Go to line 439,replace 
type Cand = () 
with 
data Cand = A | B | C | D and 
cand_all :: List Cand
cand_all =
  Prelude.error "AXIOM TO BE REALIZED" with 
cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D Nil)))

Now run 
> make runmain
>./Main
If you want to re-run the program then run 
> make cleanlib
> make cleanmain
