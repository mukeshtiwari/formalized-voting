module Lib where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f1 f2 n =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    f1)
    (\n0 ->
    f2 n0 (nat_rect f1 f2 n0))
    n

nat_rec :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rec =
  nat_rect

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f1 f2 l =
  case l of {
   [] -> f1;
   (:) y l0 -> f2 y l0 (list_rect f1 f2 l0)}

list_rec :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rec =
  list_rect

length :: ([] a1) -> Prelude.Int
length l =
  case l of {
   [] -> 0;
   (:) _ l' -> (Prelude.succ) (length l')}

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.LT -> Prelude.LT;
   Prelude.EQ -> Prelude.GT;
   Prelude.GT -> Prelude.EQ}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f1 f2 s =
  case s of {
   Prelude.True -> f1 __;
   Prelude.False -> f2 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

lt_eq_lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Maybe Prelude.Bool
lt_eq_lt_dec n m0 =
  nat_rec (\m1 ->
    (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.Just
      Prelude.False)
      (\_ -> Prelude.Just
      Prelude.True)
      m1) (\_ iHn m1 ->
    (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.Nothing)
      (\m2 ->
      iHn m2)
      m1) n m0

le_lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
le_lt_dec n m0 =
  nat_rec (\_ -> Prelude.True) (\_ iHn m1 ->
    (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.False)
      (\m2 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (iHn m2))
      m1) n m0

le_gt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
le_gt_dec n m0 =
  le_lt_dec n m0

nat_compare_alt :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
nat_compare_alt n m0 =
  case lt_eq_lt_dec n m0 of {
   Prelude.Just s ->
    case s of {
     Prelude.True -> Prelude.EQ;
     Prelude.False -> Prelude.LT};
   Prelude.Nothing -> Prelude.GT}

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x)
    (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    p)
    (\_ -> (\x -> 2 Prelude.* x)
    1)
    x

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      q)
      (\_ -> (\x -> 2 Prelude.* x)
      1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ ->
    1)
    x

compare_cont :: Prelude.Ordering -> Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont r p q)
      (\q ->
      compare_cont Prelude.GT p q)
      (\_ ->
      Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont Prelude.EQ p q)
      (\q ->
      compare_cont r p q)
      (\_ ->
      Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.EQ)
      (\_ ->
      Prelude.EQ)
      (\_ ->
      r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare =
  compare_cont Prelude.LT

list_eq_dec :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> ([] a1) -> Prelude.Bool
list_eq_dec eq_dec l l' =
  list_rect (\l'0 ->
    case l'0 of {
     [] -> Prelude.True;
     (:) _ _ -> Prelude.False}) (\a _ x l'0 ->
    case l'0 of {
     [] -> Prelude.False;
     (:) a0 l1 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (x l1)) (\_ ->
        Prelude.False) (eq_dec a a0)}) l l'

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f1 l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f1 a) (map f1 t)}

forallb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
forallb f1 l =
  case l of {
   [] -> Prelude.True;
   (:) a l0 -> (Prelude.&&) (f1 a) (forallb f1 l0)}

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x)
    p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x)
    p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    (\p -> Prelude.negate
    (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Prelude.negate
    1)
    (\p -> (\x -> x)
    (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double (pos_sub p q))
      (\q ->
      succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double (pos_sub p q))
      (\_ -> (\x -> x)
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x)
      q))
      (\q -> Prelude.negate
      (pred_double q))
      (\_ ->
      0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\x0 -> Prelude.negate
    x0)
    (\x0 -> (\x -> x)
    x0)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.LT)
      (\_ ->
      Prelude.EQ)
      (\_ ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.GT)
      (\y' ->
      compare x' y')
      (\_ ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.EQ)
      (\_ ->
      Prelude.EQ)
      (\y' ->
      compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Prelude.EQ -> Prelude.True;
   _ -> Prelude.False}

bool_of_sumbool :: Prelude.Bool -> Prelude.Bool
bool_of_sumbool h =
  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) h

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_dec x y =
  case compare0 x y of {
   Prelude.EQ -> Prelude.True;
   _ -> Prelude.False}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_ge_dec x y =
  z_lt_dec x y

z_lt_ge_bool :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

linear_search :: (Prelude.Int -> Prelude.Bool) -> Prelude.Int -> Prelude.Int
linear_search p_dec m0 =
  case p_dec m0 of {
   Prelude.True -> m0;
   Prelude.False -> linear_search p_dec ((Prelude.succ) m0)}

constructive_indefinite_ground_description_nat :: (Prelude.Int -> Prelude.Bool) -> Prelude.Int
constructive_indefinite_ground_description_nat p_dec =
  linear_search p_dec 0

p'_decidable :: (Prelude.Int -> a1) -> (a1 -> Prelude.Bool) -> Prelude.Int -> Prelude.Bool
p'_decidable g1 p_decidable n =
  p_decidable (g1 n)

constructive_indefinite_ground_description :: (a1 -> Prelude.Int) -> (Prelude.Int -> a1) -> (a1 ->
                                              Prelude.Bool) -> a1
constructive_indefinite_ground_description _ g1 p_decidable =
  let {h1 = constructive_indefinite_ground_description_nat (p'_decidable g1 p_decidable)} in g1 h1

maxlist :: ([] Prelude.Integer) -> Prelude.Integer
maxlist l =
  case l of {
   [] -> 0;
   (:) h t ->
    case t of {
     [] -> h;
     (:) _ _ -> Prelude.max h (maxlist t)}}

l9 :: ([] a1) -> (a1 -> a1 -> Prelude.Bool) -> Prelude.Integer -> (a1 -> Prelude.Integer) -> (,) 
      a1 ()
l9 l h1 s f1 =
  list_rect (\_ _ _ _ _ -> Prelude.error "absurd case") (\a l0 iHl _ h2 s0 f2 _ ->
    let {h3 = list_eq_dec h2 l0 []} in
    case h3 of {
     Prelude.True -> (,) a __;
     Prelude.False ->
      let {hm = (Prelude.>=) (f2 a) (maxlist (map f2 l0))} in
      case hm of {
       Prelude.True -> (,) a __;
       Prelude.False ->
        let {iHl0 = iHl __ h2 s0 f2 __} in
        case iHl0 of {
         (,) x0 _ -> (,) x0 __}}}) l __ h1 s f1 __



{- Try to move this definition in other file -}
data Cand = A | B | C | D | E

cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D (Cons E Nil))))
{- End of definition -}



data PathT =
   UnitT Cand Cand
 | ConsT Cand Cand Cand PathT

type Wins_type = Cand -> (,) Prelude.Integer ((,) PathT ((,) (((,) Cand Cand) -> Prelude.Bool) ()))

type Loses_type =
  (,) Prelude.Integer ((,) Cand ((,) PathT ((,) (((,) Cand Cand) -> Prelude.Bool) ())))

m :: (Cand -> Cand -> Prelude.Integer) -> Prelude.Int -> Cand -> Cand -> Prelude.Integer
m edge n c d =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    edge c d)
    (\n' ->
    Prelude.max (m edge n' c d)
      (maxlist (map (\x -> Prelude.min (edge c x) (m edge n' x d)) cand_all)))
    n

c_wins :: (Cand -> Cand -> Prelude.Integer) -> Cand -> Prelude.Bool
c_wins edge c =
  forallb (\d -> leb (m edge (length cand_all) d c) (m edge (length cand_all) c d)) cand_all

l7 :: (Cand -> Cand -> Prelude.Integer) -> Cand -> Prelude.Bool
l7 edge c =
  let {b = c_wins edge c} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

l10 :: (Cand -> Cand -> Prelude.Integer) -> (Cand -> Cand -> Prelude.Bool) -> Prelude.Int ->
       Prelude.Integer -> Cand -> Cand -> PathT
l10 edge dec_cand n s c d =
  nat_rect (\_ c0 d0 _ -> UnitT c0 d0) (\n0 iHn s0 c0 d0 _ ->
    let {
     c1 = compare0 (m edge n0 c0 d0)
            (maxlist (map (\x -> Prelude.min (edge c0 x) (m edge n0 x d0)) cand_all))}
    in
    case c1 of {
     Prelude.EQ ->
      let {h = l9 cand_all dec_cand s0 (\x -> Prelude.min (edge c0 x) (m edge n0 x d0))} in
      case h of {
       (,) x _ -> let {iHn0 = iHn s0 x d0 __} in ConsT c0 x d0 iHn0};
     _ -> iHn s0 c0 d0 __}) n s c d __

l15 :: (Cand -> Cand -> Prelude.Integer) -> (Cand -> Cand -> Prelude.Bool) -> Cand -> Cand -> (,)
       Prelude.Integer ((,) PathT ((,) (((,) Cand Cand) -> Prelude.Bool) ()))
l15 edge dec_cand c d =
  let {s = m edge (length cand_all) d c} in
  (,) s
  (let {h = l10 edge dec_cand (length cand_all) s c d} in
   (,) h ((,) (\x -> leb (m edge (length cand_all) (Prelude.fst x) (Prelude.snd x)) s) __))

constructive_deci_cand :: (Cand -> Cand -> Prelude.Integer) -> Cand -> Cand -> Prelude.Bool
constructive_deci_cand edge c d =
  let {h = z_lt_ge_bool (m edge (length cand_all) c d) (m edge (length cand_all) d c)} in
  case h of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

f0_obligation_1 :: Cand -> ([] Cand) -> Prelude.Int
f0_obligation_1 _ _ =
   (\_ -> Prelude.error "absurd case") __

f0 :: (Cand -> Cand -> Prelude.Bool) -> Cand -> ([] Cand) -> Prelude.Int
f0 dec_cand a l =
  case l of {
   [] -> f0_obligation_1 a l;
   (:) h t ->
    case dec_cand a h of {
     Prelude.True -> 0;
     Prelude.False -> (Prelude.succ) (f0 dec_cand a t)}}

f :: (Cand -> Cand -> Prelude.Bool) -> Cand -> Prelude.Int
f dec_cand c =
  f0 dec_cand c cand_all

g0_obligation_1 :: Prelude.Int -> ([] Cand) -> Prelude.Int -> Cand
g0_obligation_1 _ _ _ =
   (\_ -> false_rect) __

g0 :: Prelude.Int -> ([] Cand) -> Cand
g0 n l =
  case l of {
   [] -> g0_obligation_1 n l n;
   (:) wildcard' t ->
    (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      wildcard')
      (\n' ->
      g0 n' t)
      n}

g_obligation_1 :: Prelude.Int -> Cand
g_obligation_1 _ =
  case cand_all of {
   [] -> false_rect;
   (:) c _ -> c}

g :: Prelude.Int -> Cand
g n =
  case le_lt_dec (length cand_all) n of {
   Prelude.True -> g_obligation_1 n;
   Prelude.False -> g0 n cand_all}

l18 :: (Cand -> Cand -> Prelude.Integer) -> (Cand -> Cand -> Prelude.Bool) -> Cand -> (,)
       Prelude.Integer ((,) Cand ((,) PathT ((,) (((,) Cand Cand) -> Prelude.Bool) ())))
l18 edge dec_cand c =
  let {x = constructive_indefinite_ground_description (f dec_cand) g (constructive_deci_cand edge c)}
  in
  let {s = m edge (length cand_all) c x} in
  (,) ((Prelude.+) s ((\x -> x) 1)) ((,) x ((,)
  (l10 edge dec_cand (length cand_all) ((Prelude.+) s ((\x -> x) 1)) x c) ((,) (\x0 ->
  ltb (m edge (length cand_all) (Prelude.fst x0) (Prelude.snd x0)) ((Prelude.+) s ((\x -> x) 1)))
  __)))

wins_loses_M :: (Cand -> Cand -> Prelude.Integer) -> (Cand -> Cand -> Prelude.Bool) -> Cand ->
                Prelude.Either Wins_type Loses_type
wins_loses_M edge dec_cand c =
  let {h = l7 edge c} in
  case h of {
   Prelude.True -> Prelude.Left (l15 edge dec_cand c);
   Prelude.False -> Prelude.Right (l18 edge dec_cand c)}

type Ballot = Cand -> Prelude.Int

in_decidable :: Ballot -> ([] Cand) -> Prelude.Bool
in_decidable b l =
  list_rec Prelude.True (\a _ iHl ->
    case iHl of {
     Prelude.True ->
      let {s = le_gt_dec (b a) 0} in
      case s of {
       Prelude.True -> Prelude.False;
       Prelude.False -> Prelude.True};
     Prelude.False -> Prelude.False}) l

valid_or_invalid_ballot :: Ballot -> Prelude.Bool
valid_or_invalid_ballot b =
  in_decidable b cand_all

nty :: Cand -> Cand -> Prelude.Integer
nty _ _ =
  0

data Count =
   Ax ([] Ballot) (Cand -> Cand -> Prelude.Integer)
 | Cvalid Ballot ([] Ballot) (Cand -> Cand -> Prelude.Integer) (Cand -> Cand -> Prelude.Integer) 
 ([] Ballot) Count
 | Cinvalid Ballot ([] Ballot) (Cand -> Cand -> Prelude.Integer) ([] Ballot) Count
 | Fin (Cand -> Cand -> Prelude.Integer) ([] Ballot) (Cand -> Prelude.Bool) (Cand -> Prelude.Either
                                                                            Wins_type Loses_type) 
 Count

incdect :: Ballot -> (Cand -> Cand -> Prelude.Integer) -> Cand -> Cand -> Prelude.Integer
incdect p m0 c d =
  case nat_compare_alt (p c) (p d) of {
   Prelude.LT -> m0 c d;
   Prelude.EQ -> (Prelude.+) (m0 c d) ((\x -> x) 1);
   Prelude.GT -> (Prelude.-) (m0 c d) ((\x -> x) 1)}

extract_prog_gen :: ([] Ballot) -> ([] Ballot) -> ([] Ballot) -> (Cand -> Cand -> Prelude.Integer) ->
                    Count -> (,) ([] Ballot) ((,) (Cand -> Cand -> Prelude.Integer) Count)
extract_prog_gen _ u =
  list_rect (\inbs m0 x -> (,) inbs ((,) m0 x)) (\a u0 iHu ->
    let {h = valid_or_invalid_ballot a} in
    (\inbs m0 x ->
    case h of {
     Prelude.True -> let {x0 = Cvalid a u0 m0 (incdect a m0) inbs x} in iHu inbs (incdect a m0) x0;
     Prelude.False -> let {x0 = Cinvalid a u0 m0 inbs x} in iHu ((:) a inbs) m0 x0})) u

extract_prog :: ([] Ballot) -> (,) ([] Ballot) ((,) (Cand -> Cand -> Prelude.Integer) Count)
extract_prog bs =
  extract_prog_gen bs bs [] nty (Ax bs nty)

final_count :: (Cand -> Cand -> Prelude.Bool) -> ([] Ballot) -> (,) (Cand -> Prelude.Bool)
               ((,) Count ())
final_count dec_cand bs =
  let {x = extract_prog bs} in
  case x of {
   (,) bs' s ->
    case s of {
     (,) m0 x0 ->
      let {x1 = \_ _ -> Fin m0 bs' (c_wins m0) (wins_loses_M m0 dec_cand) x0} in
      let {x2 = x1 __ __} in (,) (c_wins m0) ((,) x2 __)}}

