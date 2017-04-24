module Main where
import qualified Prelude as P
import Lib
import Derivation
import System.IO
import qualified Data.List as L
import Control.Monad as M

haskCoq :: [a] -> List a
haskCoq [] = Nil
haskCoq (h : hs) = Cons h (haskCoq hs)

coqNat :: P.Int -> Nat
coqNat n
  | n P.== 0 = O
  | P.otherwise = S (coqNat (n P.- 1))


wordsWhen :: (P.Char -> P.Bool) -> P.String -> [P.String]
wordsWhen p s =  case L.dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = L.break p s'


balfun :: [(Cand, Nat)] -> (Ballot Cand)
balfun [(A, b1), (B, b2), (C, b3), (D, b4)] = f where
  f :: Cand -> Nat
  f A = b1
  f B = b2
  f C = b3
  f D = b4


main :: IO ()
main = do
   r <- getContents
   let votes = schulze_winners_pf  P.. haskCoq P.. P.map (balfun P..
               L.sort P.. P.map (\(y, z) -> (y, coqNat z)) P.. 
               P.map (\x -> P.read x :: (Cand, P.Int)) P.. 
               wordsWhen (P.== ';')) P.. P.lines P.$ r
   P.print votes
