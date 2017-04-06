module Main where
import qualified Prelude as P
import Lib
import Derivation
import System.IO
import Data.List as L
import System.Random.Shuffle
import Control.Monad as M
import Data.Time

haskCoq :: [a] -> List a
haskCoq [] = Nil
haskCoq (h : hs) = Cons h (haskCoq hs)

coqNat :: P.Int -> Nat
coqNat n
  | n P.== 0 = O
  | P.otherwise = S (coqNat (n P.- 1))


candEq :: Cand -> Cand -> Sumbool
candEq c d 
  | c P.== d = Left
  | P.otherwise = Right


{- Wikipedia example -}


charCand :: P.Char -> Cand
charCand 'A' = A
charCand 'B' = B
charCand 'C' = C
charCand 'D' = D
--charCand 'E' = E

balfun :: [(Cand, Nat)] -> Ballot
balfun ((A, b1) : (B, b2) : (C, b3) : (D, b4) {-: (E, b5) -}: _) = f where
  f :: Cand -> Nat
  f A = b1
  f B = b2
  f C = b3
  f D = b4
  --f E = b5


createCand :: IO ()
createCand = do
  let t = (P.replicate 4 "ABCD") P.++ (P.replicate 3 "BCAD") P.++ (P.replicate 2 "CABD") P.++ (P.replicate 1 "ACBD")
  v <- shuffleM t
  writeFile ("votes_customized.txt") (P.unlines v)
 

main :: IO ()
main = do
  {- call this function to create list of ballots -} 
   --createCand
   r <- readFile "votes_customized.txt"
   let votes = final_count candEq P.. haskCoq P.. P.map balfun P..
              P.map (P.map (\(y, z) -> (charCand y, coqNat z))) 
              P.. P.map L.sort P.. P.map (\x ->  P.zip x [1..]) P.. P.lines P.$ r
   P.print votes

