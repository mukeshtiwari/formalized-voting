module Lib where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f1 _ =
  f1

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f1 y =
  eq_rect x f1 y

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f1 f2 n =
  case n of {
   O -> f1;
   S n0 -> f2 n0 (nat_rect f1 f2 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f1 f2 l =
  case l of {
   Nil -> f1;
   Cons y l0 -> f2 y l0 (list_rect f1 f2 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f1 f2 s =
  case s of {
   Left -> f1 __;
   Right -> f2 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

lt_eq_lt_dec :: Nat -> Nat -> Sumor Sumbool
lt_eq_lt_dec n m0 =
  nat_rec (\m1 ->
    case m1 of {
     O -> Inleft Right;
     S _ -> Inleft Left}) (\_ iHn m1 ->
    case m1 of {
     O -> Inright;
     S m2 -> iHn m2}) n m0

le_lt_dec :: Nat -> Nat -> Sumbool
le_lt_dec n m0 =
  nat_rec (\_ -> Left) (\_ iHn m1 ->
    case m1 of {
     O -> Right;
     S m2 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m2)}) n m0

le_gt_dec :: Nat -> Nat -> Sumbool
le_gt_dec n m0 =
  le_lt_dec n m0

nat_compare_alt :: Nat -> Nat -> Comparison
nat_compare_alt n m0 =
  case lt_eq_lt_dec n m0 of {
   Inleft s ->
    case s of {
     Left -> Lt;
     Right -> Eq};
   Inright -> Gt}

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

list_eq_dec :: (a1 -> a1 -> Sumbool) -> (List a1) -> (List a1) -> Sumbool
list_eq_dec eq_dec l l' =
  list_rect (\l'0 ->
    case l'0 of {
     Nil -> Left;
     Cons _ _ -> Right}) (\a _ x l'0 ->
    case l'0 of {
     Nil -> Right;
     Cons a0 l1 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x l1))
        (\_ -> Right) (eq_dec a a0)}) l l'

map :: (a1 -> a2) -> (List a1) -> List a2
map f1 l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f1 a) (map f1 t)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f1 l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f1 a) (forallb f1 l0)}

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add0 :: Z -> Z -> Z
add0 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

sub :: Z -> Z -> Z
sub m0 n =
  add0 m0 (opp n)

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos _ -> Lt;
     Zneg _ -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

leb :: Z -> Z -> Bool
leb x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: Z -> Z -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

max :: Z -> Z -> Z
max n m0 =
  case compare0 n m0 of {
   Lt -> m0;
   _ -> n}

min :: Z -> Z -> Z
min n m0 =
  case compare0 n m0 of {
   Gt -> m0;
   _ -> n}

bool_of_sumbool :: Sumbool -> Bool
bool_of_sumbool h =
  sumbool_rec (\_ -> True) (\_ -> False) h

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_ge_dec :: Z -> Z -> Sumbool
z_ge_dec x y =
  case compare0 x y of {
   Lt -> Right;
   _ -> Left}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec x y =
  z_lt_dec x y

z_ge_lt_dec :: Z -> Z -> Sumbool
z_ge_lt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_ge_dec x y)

z_lt_ge_bool :: Z -> Z -> Bool
z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

linear_search :: (Nat -> Sumbool) -> Nat -> Nat
linear_search p_dec m0 =
  case p_dec m0 of {
   Left -> m0;
   Right -> linear_search p_dec (S m0)}

constructive_indefinite_ground_description_nat :: (Nat -> Sumbool) -> Nat
constructive_indefinite_ground_description_nat p_dec =
  linear_search p_dec O

p'_decidable :: (Nat -> a1) -> (a1 -> Sumbool) -> Nat -> Sumbool
p'_decidable g1 p_decidable n =
  p_decidable (g1 n)

constructive_indefinite_ground_description :: (a1 -> Nat) -> (Nat -> a1) ->
                                              (a1 -> Sumbool) -> a1
constructive_indefinite_ground_description _ g1 p_decidable =
  let {
   h1 = constructive_indefinite_ground_description_nat
          (p'_decidable g1 p_decidable)}
  in
  g1 h1

maxlist :: (List Z) -> Z
maxlist l =
  case l of {
   Nil -> Z0;
   Cons h t ->
    case t of {
     Nil -> h;
     Cons _ _ -> max h (maxlist t)}}

l9 :: (List a1) -> (a1 -> a1 -> Sumbool) -> Z -> (a1 -> Z) -> SigT a1 ()
l9 l h1 s f1 =
  list_rect (\_ _ _ _ _ -> Prelude.error "absurd case")
    (\a l0 iHl _ h2 s0 f2 _ ->
    let {h3 = list_eq_dec h2 l0 Nil} in
    case h3 of {
     Left -> ExistT a __;
     Right ->
      let {hm = z_ge_lt_dec (f2 a) (maxlist (map f2 l0))} in
      case hm of {
       Left -> ExistT a __;
       Right ->
        let {iHl0 = iHl __ h2 s0 f2 __} in
        case iHl0 of {
         ExistT x0 _ -> ExistT x0 __}}}) l __ h1 s f1 __


{-
{- Try to move this definition in other file -}
data Cand = A | B | C | D | E

cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D (Cons E Nil))))
{- End of definition -}
-}

data Cand = A | B | C | D

cand_all :: List Cand
cand_all = Cons A (Cons B (Cons C (Cons D Nil)))

data PathT =
   UnitT Cand Cand
 | ConsT Cand Cand Cand PathT

type Wins_type =
  Cand -> SigT Z (Prod PathT (SigT ((Prod Cand Cand) -> Bool) ()))

type Loses_type =
  SigT Z (SigT Cand (Prod PathT (SigT ((Prod Cand Cand) -> Bool) ())))

m :: (Cand -> Cand -> Z) -> Nat -> Cand -> Cand -> Z
m marg n c d =
  case n of {
   O -> marg c d;
   S n' ->
    max (m marg n' c d)
      (maxlist (map (\x -> min (marg c x) (m marg n' x d)) cand_all))}

c_wins :: (Cand -> Cand -> Z) -> Cand -> Bool
c_wins marg c =
  forallb (\d ->
    leb (m marg (length cand_all) d c) (m marg (length cand_all) c d))
    cand_all

l7 :: (Cand -> Cand -> Z) -> Cand -> Sumbool
l7 marg c =
  let {b = c_wins marg c} in
  case b of {
   True -> Left;
   False -> Right}

l10 :: (Cand -> Cand -> Sumbool) -> (Cand -> Cand -> Z) -> Nat -> Z -> Cand
       -> Cand -> PathT
l10 dec_cand marg n s c d =
  nat_rect (\_ c0 d0 _ -> UnitT c0 d0) (\n0 iHn s0 c0 d0 _ ->
    let {
     c1 = compare0 (m marg n0 c0 d0)
            (maxlist (map (\x -> min (marg c0 x) (m marg n0 x d0)) cand_all))}
    in
    case c1 of {
     Lt ->
      let {
       h = l9 cand_all dec_cand s0 (\x -> min (marg c0 x) (m marg n0 x d0))}
      in
      case h of {
       ExistT x _ -> let {iHn0 = iHn s0 x d0 __} in ConsT c0 x d0 iHn0};
     _ -> iHn s0 c0 d0 __}) n s c d __

l15 :: (Cand -> Cand -> Sumbool) -> (Cand -> Cand -> Z) -> Cand -> Wins_type
l15 dec_cand marg c d =
  let {s = m marg (length cand_all) c d} in
  ExistT s
  (let {h1 = l10 dec_cand marg (length cand_all) s c d} in
   Pair h1 (ExistT (\x -> leb (m marg (length cand_all) (fst x) (snd x)) s)
   __))

constructive_deci_cand :: (Cand -> Cand -> Z) -> Cand -> Cand -> Sumbool
constructive_deci_cand marg c d =
  let {
   h = z_lt_ge_bool (m marg (length cand_all) c d)
         (m marg (length cand_all) d c)}
  in
  case h of {
   True -> Left;
   False -> Right}

f0_obligation_1 :: Cand -> (List Cand) -> Nat
f0_obligation_1 _ l =
  eq_rec Nil (\_ -> Prelude.error "absurd case") l __

f0 :: (Cand -> Cand -> Sumbool) -> Cand -> (List Cand) -> Nat
f0 dec_cand a l =
  case l of {
   Nil -> f0_obligation_1 a l;
   Cons h t ->
    case dec_cand a h of {
     Left -> O;
     Right -> S (f0 dec_cand a t)}}

f :: (Cand -> Cand -> Sumbool) -> Cand -> Nat
f dec_cand c =
  f0 dec_cand c cand_all

g0_obligation_1 :: Nat -> (List Cand) -> Nat -> Cand
g0_obligation_1 _ l _ =
  eq_rect Nil (\_ -> false_rect) l __

g0 :: Nat -> (List Cand) -> Cand
g0 n l =
  case l of {
   Nil -> g0_obligation_1 n l n;
   Cons wildcard' t ->
    case n of {
     O -> wildcard';
     S n' -> g0 n' t}}

g_obligation_1 :: Nat -> Cand
g_obligation_1 _ =
  case cand_all of {
   Nil -> false_rect;
   Cons c _ -> c}

g :: Nat -> Cand
g n =
  case le_lt_dec (length cand_all) n of {
   Left -> g_obligation_1 n;
   Right -> g0 n cand_all}

l18 :: (Cand -> Cand -> Sumbool) -> (Cand -> Cand -> Z) -> Cand -> Loses_type
l18 dec_cand marg c =
  let {
   x = constructive_indefinite_ground_description (f dec_cand) g
         (constructive_deci_cand marg c)}
  in
  let {s = m marg (length cand_all) x c} in
  ExistT s (ExistT x (Pair (l10 dec_cand marg (length cand_all) s x c)
  (ExistT (\x0 -> ltb (m marg (length cand_all) (fst x0) (snd x0)) s) __)))

wins_loses_M :: (Cand -> Cand -> Sumbool) -> (Cand -> Cand -> Z) -> Cand ->
                Sum Wins_type Loses_type
wins_loses_M dec_cand marg c =
  let {h = l7 marg c} in
  case h of {
   Left -> Inl (l15 dec_cand marg c);
   Right -> Inr (l18 dec_cand marg c)}

type Ballot = Cand -> Nat

in_decidable :: Ballot -> (List Cand) -> Sumbool
in_decidable b l =
  list_rec Left (\a _ iHl ->
    case iHl of {
     Left ->
      let {s = le_gt_dec (b a) O} in
      case s of {
       Left -> Right;
       Right -> Left};
     Right -> Right}) l

valid_or_invalid_ballot :: Ballot -> Sumbool
valid_or_invalid_ballot b =
  in_decidable b cand_all

nty :: Cand -> Cand -> Z
nty _ _ =
  Z0

data Count =
   Ax (List Ballot) (Cand -> Cand -> Z)
 | Cvalid Ballot (List Ballot) (Cand -> Cand -> Z) (Cand -> Cand -> Z) 
 (List Ballot) Count
 | Cinvalid Ballot (List Ballot) (Cand -> Cand -> Z) (List Ballot) Count
 | Fin (Cand -> Cand -> Z) (List Ballot) (Cand -> Bool) (Cand -> Sum
                                                        Wins_type Loses_type) 
 Count

incdect :: Ballot -> (Cand -> Cand -> Z) -> Cand -> Cand -> Z
incdect p m0 c d =
  case nat_compare_alt (p c) (p d) of {
   Eq -> m0 c d;
   Lt -> add0 (m0 c d) (Zpos XH);
   Gt -> sub (m0 c d) (Zpos XH)}

extract_prog_gen :: (List Ballot) -> (List Ballot) -> (List Ballot) -> (Cand
                    -> Cand -> Z) -> Count -> SigT (List Ballot)
                    (SigT (Cand -> Cand -> Z) Count)
extract_prog_gen _ u =
  list_rect (\inbs m0 x -> ExistT inbs (ExistT m0 x)) (\a u0 iHu ->
    let {h = valid_or_invalid_ballot a} in
    (\inbs m0 x ->
    case h of {
     Left ->
      let {x0 = Cvalid a u0 m0 (incdect a m0) inbs x} in
      iHu inbs (incdect a m0) x0;
     Right -> let {x0 = Cinvalid a u0 m0 inbs x} in iHu (Cons a inbs) m0 x0}))
    u

extract_prog :: (List Ballot) -> SigT (List Ballot)
                (SigT (Cand -> Cand -> Z) Count)
extract_prog bs =
  extract_prog_gen bs bs Nil nty (Ax bs nty)

final_count :: (Cand -> Cand -> Sumbool) -> (List Ballot) -> SigT
               (Cand -> Bool) (SigT Count ())
final_count dec_cand bs =
  let {x = extract_prog bs} in
  case x of {
   ExistT bs' s ->
    case s of {
     ExistT m0 x0 ->
      let {x1 = Fin m0 bs' (c_wins m0) (wins_loses_M dec_cand m0) x0} in
      ExistT (c_wins m0) (ExistT x1 __)}}

