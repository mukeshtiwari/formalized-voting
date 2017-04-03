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
charCand 'E' = E

balfun :: [(Cand, Nat)] -> Ballot
balfun ((A, b1) : (B, b2) : (C, b3) : (D, b4) : (E, b5) : _) = f where
  f :: Cand -> Nat
  f A = b1
  f B = b2
  f C = b3
  f D = b4
  f E = b5


createCand :: P.Int -> IO ()
createCand n = do 
  t <- mapM shuffleM (P.replicate n "ABCDE")
  writeFile ("votes_" P.++ P.show n P.++ ".txt") (P.unlines t)
 

main :: IO ()
main = do
  {- call this function to create list of ballots -} 
  -- createCand 10000
  P.flip forM_ (\x -> do
   P.putStrLn ("Starting computation for file " P.++ x P.++ "\n\n\n")
   start <- getCurrentTime
   r <- readFile x
   let votes = final_count candEq P.. haskCoq P.. P.map balfun P..
              P.map (P.map (\(y, z) -> (charCand y, coqNat z))) 
              P.. P.map L.sort P.. P.map (\x ->  P.zip x [1..]) P.. P.lines P.$ r
   P.print votes
   end <- getCurrentTime
   P.putStr ("Time consume for file " P.++ x P.++ " = ") 
   P.print (diffUTCTime end start)
   P.putStrLn "\n\n\n" ) ["votes_wiki.txt", "votes_100.txt", "votes_200.txt", "votes_300.txt", "votes_400.txt", "votes_500.txt", "votes_1000.txt", "votes_2000.txt", "votes_3000.txt"
   , "votes_4000.txt", "votes_5000.txt", "votes_6000.txt", "votes_7000.txt", "votes_8000.txt", "votes_9000.txt", "votes_10000.txt"]

