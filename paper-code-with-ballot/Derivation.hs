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
  show (ExistT f (ExistT v _)) = P.show v


show_winner :: Wins_type -> Cand -> [Cand] -> P.String
show_winner g x [] = ""
show_winner g x (y : ys) =
  case (g y) of 
   (ExistT u (Pair v (ExistT f _))) -> 
    "   for " P.++ P.show y P.++ ": " P.++ "path " P.++ P.show v P.++ " of strenght "  P.++ P.show (haskZ u) P.++  ", " P.++ 
    P.show (1 P.+ haskZ u) P.++ "-" P.++ "coclosed set: " P.++ P.show (P.filter (\(xx, yy) -> f (Pair xx yy) P.== True) [(a, b) | a <- (c2hl cand_all), b <- (c2hl cand_all), a P./= b])
    P.++ "\n" P.++ show_winner g x ys


show_loser :: Loses_type -> Cand -> P.String
show_loser g x = 
  case g of 
   (ExistT u (ExistT c (Pair p (ExistT f _)))) -> 
    "   for " P.++ P.show c P.++ ": " P.++ "path " P.++ P.show p P.++ " of strength >= " P.++ P.show (haskZ u) P.++ ", " P.++
    P.show (haskZ u) P.++ "-" P.++ "coclosed set: " P.++ P.show (P.filter (\(xx, yy) -> f (Pair xx yy) P.== True) [(a, b) | a <- (c2hl cand_all), b <- (c2hl cand_all), a P./= b])


show_cand :: (Cand -> Sum Wins_type Loses_type) -> Cand -> P.String
show_cand f x =
   case (f x) of
    Inl g -> "winning: " P.++ P.show x  P.++ "\n" P.++ show_winner g x (P.filter (\y -> y P./= x) (c2hl cand_all))
    Inr h -> "losing: "  P.++ P.show x  P.++ "\n" P.++ show_loser h x

show_ballot :: Ballot -> P.String
show_ballot f = P.unwords (P.map (\x -> P.show x P.++ P.show (haskInt (f x)))  (c2hl cand_all))

show_list_ballot :: List Ballot -> P.String
show_list_ballot ls = P.show (P.map show_ballot (c2hl ls))

show_marg :: (Cand -> Cand -> Z) -> P.String
show_marg m = "[" P.++ P.unwords (P.map (\(x, y) -> P.show x P.++ P.show y P.++ ":" P.++ P.show (haskZ (m x y))) [(a, b) | a <- (c2hl cand_all), b <- (c2hl cand_all), b P.> a]) P.++ "]"

bool_b :: List Ballot -> P.Bool
bool_b Nil = P.True
bool_b _ = P.False

instance P.Show Count where
  show (Ax ls m) = ""
  show (Cvalid u us m nm inbs c) = P.show c P.++ "V = [" P.++ show_ballot u P.++ (if bool_b us P.== P.True then "]" else ",....]") P.++ ", I = " P.++ show_list_ballot inbs  P.++ ", M = " P.++ show_marg m
                                      P.++ "\n----------------------------------------------------------------------------------------------------------------------------------------------------\n"
  show (Cinvalid u us m inbs c) = P.show c P.++ "I = [" P.++ show_ballot u P.++ (if bool_b us P.== P.True then "]" else ",....]") P.++ ", I = " P.++ show_list_ballot inbs P.++ ", M = " P.++ show_marg m
                                      P.++ "\n----------------------------------------------------------------------------------------------------------------------------------------------------\n"
  show (Fin m ls p f c) =  P.show c P.++ "V = [], I = " P.++ show_list_ballot ls P.++ ", M = " P.++ show_marg m
                                    P.++ "\n----------------------------------------------------------------------------------------------------------------------------------------------------\n"
                                    P.++ (P.unlines P.$ P.map (show_cand f) (c2hl cand_all))



