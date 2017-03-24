module Cand where

data List a =
   Nil
 | Cons a (List a)

data Cand = A | B | C | D | E

cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D (Cons E Nil))))

