{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
module Derivation where
import qualified Prelude as P
import Lib

c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x : (c2hl xs)

deriving instance (P.Eq Cand)
deriving instance (P.Ord Cand)
deriving instance (P.Show Cand)
deriving instance (P.Show Bool)
deriving instance (P.Eq Bool)
deriving instance (P.Show Nat)
deriving instance (P.Eq Nat)
deriving instance (P.Ord Nat)
deriving instance (P.Show a, P.Show b) => P.Show (Sum a b)
deriving instance (P.Show a, P.Show b) => P.Show (Prod a b)
  -- show (Pair a b) = "(" P.++ P.show a P.++ ", " P.++ P.show b ")"

deriving instance (P.Show a) => P.Show (List a)
deriving instance (P.Show Comparison)
deriving instance (P.Show Sumbool)
deriving instance (P.Show a) => P.Show (Sumor a)
deriving instance (P.Show Positive)
deriving instance (P.Show Z)


haskInt :: Nat -> P.Int
haskInt O = 0
haskInt (S p) = 1 P.+ haskInt p

haskPos :: Positive -> P.Int
haskPos XH = 1
haskPos p = haskHelp p 1 where
  haskHelp XH p2 = p2
  haskHelp (XO r) p2 = haskHelp r (2 P.* p2)
  haskHelp (XI r) p2 = p2 P.+ haskHelp r (2 P.* p2)


haskZ :: Z -> P.Int
haskZ Z0 = 0
haskZ (Zpos p) = haskPos p
haskZ (Zneg p) = -1 P.* haskPos p


instance P.Show PathT where
  show (UnitT x y) = P.show x P.++ " --> " P.++ P.show y
  show (ConsT x _ _ p) = P.show x P.++ " --> " P.++ P.show p

-- deriving instance (P.Show PathT)
instance P.Show (SigT (Cand -> Bool) (SigT Count ())) where
  show (ExistT f (ExistT v _)) = {- P.unlines (P.map (\x -> P.show x P.++ " ---> " P.++ if (f x) P.== True then "Winner" else "Loser") (c2hl cand_all)) P.++ "\n\n" P.++ -} P.show v


show_winner :: Wins_type -> Cand -> [Cand] -> P.String
show_winner g x [] = ""
show_winner g x (y : ys) =
  case (g y) of 
   (ExistT u (Pair v (ExistT f _))) -> 
    "Candidate = " P.++ P.show y P.++ "\n" P.++ 
    "Strength = " P.++ " " P.++ P.show (haskZ u) P.++ "\n" P.++ 
    "Path from " P.++ P.show x P.++ " to " P.++ P.show y P.++ " = " P.++ P.show v P.++ "\n" P.++ 
    "coclosed set = " P.++ P.show (P.filter (\x -> f x P.== True) [Pair a b | a <- (c2hl cand_all), b <- (c2hl cand_all), a P./= b]) P.++ 
    "\n------------\n" P.++ show_winner g x ys


show_loser :: Loses_type -> Cand -> P.String
show_loser g x = 
  case g of 
   (ExistT u (ExistT c (Pair p (ExistT f _)))) -> 
    "Strength = " P.++ P.show (haskZ u) P.++ "\n" P.++ 
    "Candidate that beats " P.++ P.show x P.++ " = " P.++ P.show c P.++ "\n" P.++ 
    "Path from " P.++ P.show c P.++ " to " P.++ P.show x P.++ " = " P.++ P.show p P.++ "\n" P.++
    "coclosed set = " P.++ P.show (P.filter (\x -> f x P.== True) [Pair a b | a <- (c2hl cand_all), b <- (c2hl cand_all), a P./= b]) P.++ 
    "\n-----------" 


show_cand :: (Cand -> Sum Wins_type Loses_type) -> Cand -> P.String
show_cand f x =
   case (f x) of
    Inl g -> "Winner " P.++ P.show x P.++ "\n-----------\n" P.++ show_winner g x (P.filter (\y -> y P./= x) (c2hl cand_all)) P.++ "\n"
    Inr h -> "Loser " P.++ P.show x P.++ "\n-----------\n" P.++ show_loser h x P.++ "\n"

show_ballot :: Ballot -> P.String
show_ballot f = P.unwords (P.map (\x -> "(" P.++ P.show x P.++ ", " P.++ P.show (haskInt (f x)) P.++ ")")  (c2hl cand_all))

show_list_ballot :: List Ballot -> P.String
show_list_ballot ls = P.show (P.map show_ballot (c2hl ls))

show_marg :: (Cand -> Cand -> Z) -> P.String
show_marg m = P.show (P.map (\(x, y) -> "marg " P.++ P.show x P.++ " " P.++ P.show y P.++ " = " P.++ P.show (haskZ (m x y))) [(a, b) | a <- (c2hl cand_all), b <- (c2hl cand_all), a P./= b])

instance P.Show Count where
  show (Ax ls m) = "Initial Votes\n" P.++ show_list_ballot ls P.++ "\nInitial Margin function\n" P.++ show_marg m P.++ "\n"
  show (Cvalid u us m nm inbs c) = P.show c P.++ "\nCounting ballot " P.++ show_ballot u P.++ "\nRemaining Ballots = " P.++ show_list_ballot us P.++ 
                                                 "\nOld Margin = " P.++ show_marg m P.++ "\nNew Margin = " P.++ show_marg nm P.++ "\nInvalid Votes = " P.++ show_list_ballot inbs  
  show (Cinvalid u us m inbs c) = P.show c P.++ "\nInvalid ballot " P.++ show_ballot u P.++ "\nRemaining Ballots = " P.++ show_list_ballot us P.++
                                                "\nPrevious Margin = " P.++ show_marg m P.++ "\nInvalid votes = " P.++ show_list_ballot inbs 
  show (Fin m ls p f c) =  P.show c P.++ " " P.++ show_marg m P.++ " " P.++ (P.unlines P.$ P.map (show_cand f) (c2hl cand_all))



