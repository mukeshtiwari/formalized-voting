{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
module Derivation where
import qualified Prelude as P
import Lib

{-
c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x : (c2hl xs)
-}
deriving instance (P.Eq Cand)
deriving instance (P.Ord Cand)
deriving instance (P.Show Cand)
--deriving instance (P.Show Bool)
--deriving instance (P.Eq Bool)
--deriving instance (P.Show Nat)
--deriving instance (P.Eq Nat)
--deriving instance (P.Ord Nat)
--deriving instance (P.Show a, P.Show b) => P.Show (Sum a b)
--deriving instance (P.Show a, P.Show b) => P.Show (Prod a b)
  -- show (Pair a b) = "(" P.++ P.show a P.++ ", " P.++ P.show b ")"

--deriving instance (P.Show a) => P.Show (List a)
--deriving instance (P.Show Comparison)
--deriving instance (P.Show Sumbool)
--deriving instance (P.Show a) => P.Show (Sumor a)
--deriving instance (P.Show Positive)
--deriving instance (P.Show Z)

instance P.Show PathT where
  show (UnitT x y) = P.show x P.++ " --> " P.++ P.show y
  show (ConsT x _ _ p) = P.show x P.++ " --> " P.++ P.show p

-- deriving instance (P.Show PathT)
instance  {-# OVERLAPPING #-} P.Show (Cand -> P.Bool, (Count, ())) where
  show (f, (v, _)) = P.show (P.map (\x -> P.show x P.++ " ---> " P.++ if (f x) P.== P.True then "Winner" else "Loser") cand_all) P.++ "\n\n" P.++ P.show v


show_winner :: Wins_type -> Cand -> [Cand] -> P.String
show_winner g x [] = ""
show_winner g x (y : ys) =
  case (g y) of 
   (u, (v, (f, _))) -> 
    "Candidate = " P.++ P.show y P.++ "\n" P.++ 
    "Strength = " P.++ " " P.++ P.show u P.++ "\n" P.++ 
    "Path from " P.++ P.show x P.++ " to " P.++ P.show y P.++ " = " P.++ P.show v P.++ "\n" P.++ 
    "coclosed set = " P.++ P.show (P.filter (\x -> f x P.== P.True) [(a, b) | a <- cand_all, b <- cand_all, a P./= b]) P.++ 
    "\n------------\n" P.++ show_winner g x ys


show_loser :: Loses_type -> Cand -> P.String
show_loser g x = 
  case g of 
   (u, (c, (p, (f, _)))) -> 
    "Strength = " P.++ P.show u P.++ "\n" P.++ 
    "Candidate that beats " P.++ P.show x P.++ " = " P.++ P.show c P.++ "\n" P.++ 
    "Path from " P.++ P.show c P.++ " to " P.++ P.show x P.++ " = " P.++ P.show p P.++ "\n" P.++
    "coclosed set = " P.++ P.show (P.filter (\x -> f x P.== P.True) [(a, b) | a <- cand_all, b <- cand_all, a P./= b]) P.++ 
    "\n-----------" 


show_cand :: (Cand -> P.Either Wins_type Loses_type) -> Cand -> P.String
show_cand f x =
   case (f x) of
    P.Left g -> "Winner " P.++ P.show x P.++ "\n-----------\n" P.++ show_winner g x (P.filter (\y -> y P./= x) cand_all) P.++ "\n"
    P.Right h -> "Loser " P.++ P.show x P.++ "\n-----------\n" P.++ show_loser h x P.++ "\n"

instance P.Show Count where
  show (Ax _ _) = "x"
  show (Cvalid _ _ _ _ _ _) = "Valid"
  show (Cinvalid _ _ _ _ _) = "Invalid"
  show (Fin _ _ _ f _) =  P.unlines P.$ P.map (show_cand f) cand_all



