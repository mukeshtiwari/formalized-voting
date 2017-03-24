{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
module Derivation where
import qualified Prelude as P
import Cand
import Lib

c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x:(c2hl xs)

deriving instance (P.Eq Cand)
deriving instance (P.Ord Cand)
deriving instance (P.Show Cand)
deriving instance (P.Show Bool)
deriving instance (P.Show Nat)
deriving instance (P.Eq Nat)
deriving instance (P.Ord Nat)

{- for the moment assume the instance -}
instance (P.Show a, P.Show b) => P.Show (Sum a b) where
  show (Inl f) = "Winner " P.++ P.show f P.++ "\n"
  show (Inr f) = "Loser " P.++ P.show f  P.++ "\n"

deriving instance (P.Show a, P.Show b) => P.Show (Prod a b)
deriving instance (P.Show a) => P.Show (List a)
deriving instance (P.Show Comparison)

instance (P.Show a) => P.Show (Cand -> a) where
  show f = show_l (c2hl cand_all) where
    show_l [] = ""
    show_l [c] = (P.show c) P.++ "[" P.++ (P.show (f c)) P.++ "]"
    show_l (c:cs) = (P.show c) P.++ "[" P.++ (P.show (f c)) P.++ "] " P.++ (show_l cs) 


instance (P.Show a) => P.Show ((Prod Cand Cand) -> a) where
  show f = show_l [(Pair a b) | a <- (c2hl cand_all), b <- (c2hl cand_all)] where
    show_l [] = ""
    show_l [c] = (P.show c) P.++ "[" P.++ (P.show (f c)) P.++ "]"
    show_l (c:cs) = (P.show c) P.++ "[" P.++ (P.show (f c)) P.++ "] " P.++ (show_l cs)

{-
instance (P.Show a, P.Show p) => P.Show (SigT a p) where
  show (ExistT a p) = P.show a P.++ " " P.++ P.show p 
--}

instance (P.Show a) => P.Show (SigT Z (Prod PathT (SigT a ()))) where
  show (ExistT v (Pair x (ExistT y _))) = P.show v P.++ "  " P.++ P.show x P.++ " " P.++ P.show y

instance (P.Show a) => P.Show (SigT Z (SigT Cand (Prod PathT (SigT a ())))) where
  show (ExistT v (ExistT c (Pair x (ExistT y _)))) = P.show v P.++ " " P.++ P.show c P.++ " " P.++ P.show x P.++ " " P.++ P.show y

instance P.Show (SigT Count ()) where
  show (ExistT v _) = P.show v

deriving instance (P.Show Sumbool)
deriving instance (P.Show a) => P.Show (Sumor a)
deriving instance (P.Show Positive)
deriving instance (P.Show Z)
deriving instance (P.Show PathT)

{- assume it for the moment -}
instance P.Show Count where 
  show (Ax _ _) = "x"
  show (Cvalid _ _ _ _ _ _) = "Valid"
  show (Cinvalid _ _ _ _ _) = "Invalid"
  show (Fin _ _ _ f) =  "A: " P.++ (P.show (f A)) P.++
                        "B: " P.++ (P.show (f B)) P.++
                        "C: " P.++ (P.show (f C)) P.++
                        "D: " P.++ (P.show (f D)) P.++
                        "E: " P.++ (P.show (f E)) 


