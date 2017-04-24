module Main where
import Control.DeepSeq
import qualified Prelude as P
import LibNative
import DerivationNative
import System.IO
import Data.List as L
import Control.Monad as M

haskCoq :: [a] -> List a
haskCoq [] = Nil
haskCoq (h : hs) = Cons h (haskCoq hs)


wordsWhen :: (P.Char -> P.Bool) -> P.String -> [P.String]
wordsWhen p s =  
    case L.dropWhile p s of 
            "" -> []
            s' -> w : wordsWhen p s'' where (w, s'') = L.break p s'


balfun :: [(Cand, P.Int)] -> (Ballot Cand)
balfun [(A, b1), (B, b2), (C, b3), (D, b4)] = f where
  f :: Cand -> P.Int
  f A = b1
  f B = b2
  f C = b3
  f D = b4
  


main :: IO ()
main = do
   r <- getContents
   let ballots = P.map (balfun P.. L.sort  P.. 
                        P.map (\x -> P.read x :: (Cand, P.Int)) P.. wordsWhen (P.== ';')) P.. P.lines P.$ r
   deepseq ballots (return ())
   let votes = schulze_winners_pf  (haskCoq ballots)
   P.print votes

