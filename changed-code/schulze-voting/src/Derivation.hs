{-# Language StandaloneDeriving #-}
module Derivation where
import qualified Prelude as P
import Cand
import Lib

deriving instance (P.Eq Cand)
deriving instance (P.Ord Cand)
deriving instance (P.Show Cand)
deriving instance (P.Show Bool)
deriving instance (P.Show Nat)
deriving instance (P.Eq Nat)
deriving instance (P.Ord Nat)

{- for the moment assume the instance -}
instance P.Show (Sum a b) where
  show (Inl _) = "Left"
  show (Inr _) = "Right"

deriving instance (P.Show a, P.Show b) => P.Show (Prod a b)
deriving instance (P.Show a) => P.Show (List a)
deriving instance (P.Show Comparison)

{- assume it for the moment -}
instance (P.Show a) => P.Show (SigT a p) where
  show (ExistT a p) = P.show a

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


