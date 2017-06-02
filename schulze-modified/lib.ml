type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m0 =
  match l with
  | Nil -> m0
  | Cons (a, l1) -> Cons (a, (app l1 m0))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m0 =
    match n with
    | O -> True
    | S n' ->
      (match m0 with
       | O -> False
       | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m0 =
    leb (S n) m0

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m0 =
    match n with
    | O ->
      (match m0 with
       | O -> Left
       | S _ -> Right)
    | S n0 ->
      (match m0 with
       | O -> Right
       | S m1 -> eq_dec n0 m1)
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) ->
  (match f a with
   | True -> forallb f l0
   | False -> False)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m0 n =
    add m0 (opp n)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos _ -> Lt
       | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val max : z -> z -> z **)

  let max n m0 =
    match compare n m0 with
    | Lt -> m0
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m0 =
    match compare n m0 with
    | Gt -> m0
    | _ -> n
 end

(** val bool_of_sumbool : sumbool -> bool **)

let bool_of_sumbool = function
| Left -> True
| Right -> False

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_ge_dec : z -> z -> sumbool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> Right
  | _ -> Left

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec x y =
  z_lt_dec x y

(** val z_ge_lt_dec : z -> z -> sumbool **)

let z_ge_lt_dec x y =
  z_ge_dec x y

(** val z_lt_ge_bool : z -> z -> bool **)

let z_lt_ge_bool x y =
  bool_of_sumbool (z_lt_ge_dec x y)

(** val all_pairs : 'a1 list -> ('a1, 'a1) prod list **)

let rec all_pairs = function
| Nil -> Nil
| Cons (c, cs) ->
  Cons ((Pair (c, c)),
    (app (all_pairs cs)
      (app (map (fun x -> Pair (c, x)) cs) (map (fun x -> Pair (x, c)) cs))))

(** val maxlist : z list -> z **)

let rec maxlist = function
| Nil -> Z0
| Cons (h, t) ->
  (match t with
   | Nil -> h
   | Cons (_, _) -> Z.max h (maxlist t))

(** val max_of_nonempty_list_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> z -> ('a1 -> z) -> ('a1, __) sigT **)

let max_of_nonempty_list_type l h1 s f =
  let rec f0 l0 h2 s0 f1 =
    match l0 with
    | Nil -> assert false (* absurd case *)
    | Cons (h, t) ->
      (match t with
       | Nil -> (fun _ -> ExistT (h, __))
       | Cons (h3, t1) ->
         let hmax = z_ge_lt_dec (f1 h) (maxlist (map f1 (Cons (h3, t1)))) in
         (fun _ ->
         match hmax with
         | Left -> ExistT (h, __)
         | Right ->
           let f2 = f0 t h2 s0 f1 __ in
           let ExistT (x, _) = f2 in ExistT (x, __)))
  in f0 l h1 s f __

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT

type 'cand wins_type =
  'cand -> (z, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT

type 'cand loses_type =
  (z, ('cand, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod)
  sigT) sigT

(** val m : 'a1 list -> ('a1 -> 'a1 -> z) -> nat -> 'a1 -> 'a1 -> z **)

(* customized code for building table bottom up *)
let listify cand_all0 m0 =
  map (fun s -> Pair ((Pair ((fst s), (snd s))), (m0 (fst s) (snd s))))
    (all_pairs cand_all0)

(** val linear_search_v :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> z) -> (('a1, 'a1)
    prod, z) prod list -> z **)

let rec linear_search dec_cand c d m0 = function
| Nil -> m0 c d
| Cons (y, t) ->
  let Pair (y0, k) = y in
  let Pair (c1, c2) = y0 in
  (match dec_cand c c1 with
   | Left ->
     (match dec_cand d c2 with
      | Left -> k
      | Right -> linear_search dec_cand c d m0 t)
   | Right -> linear_search dec_cand c d m0 t)

        
let rec build_new_list cand_all0 dec_cand m0 t1 t2 =
  match t1 with
  | Nil -> Nil
  | Cons (y, t) ->
     let Pair (y0, v) = y in
     let Pair (c, d) = y0 in
     let new_val =
       Z.max v (maxlist
                  (map (fun x -> Z.min (m0 c x) (linear_search dec_cand x d m0 t2)) cand_all0)) in
     Cons (Pair (Pair (c, d), new_val), build_new_list cand_all0 dec_cand m0 t t2)
           
let rec mm cand_all0 dec_cand m0 n t =
  match n with
  | O -> t
  | S n' ->
     let u = build_new_list cand_all0 dec_cand m0 t t in
     mm cand_all0 dec_cand m0 n' u

let rec m_new dec_cand cand_all0 marg n c d =
  let t = listify cand_all0 marg in
  let nt = mm cand_all0 dec_cand marg n t in
  linear_search dec_cand c d marg nt
(* end of customized code *)
                  
let rec m dec_cand cand_all0 marg n c d =
  m_new dec_cand cand_all0 marg n c d
        (*
  match n with
  | O -> marg c d
  | S n' ->
    Z.max (m cand_all0 marg n' c d)
      (maxlist
        (map (fun x -> Z.min (marg c x) (m cand_all0 marg n' x d)) cand_all0))
         *)
      

(** val iterated_marg_patht :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> z ->
    'a1 -> 'a1 -> 'a1 pathT **)

let rec iterated_marg_patht cand_all0 dec_cand marg n s c d nt =
  match n with
  | O -> UnitT (c, d)
  | S n' ->
     let t1 = linear_search dec_cand c d marg nt (* m dec_cand cand_all0 marg n' c d *)in
    let t2 =
      maxlist
        (map (fun x -> Z.min (marg c x)
                             (linear_search dec_cand x d marg nt (* m dec_cand cand_all0 marg n' x d*)  )) cand_all0)
    in
    let cm = Z.compare t1 t2 in
    (match cm with
     | Lt ->
       let ExistT (x, _) =
         max_of_nonempty_list_type cand_all0 dec_cand s (fun x ->
                                     Z.min (marg c x) (linear_search dec_cand x d marg nt (*m dec_cand cand_all0 marg n' x d*)))
       in
       ConsT (c, x, d,
       (iterated_marg_patht cand_all0 dec_cand marg n' s x d nt))
     | _ -> iterated_marg_patht cand_all0 dec_cand marg n' s c d nt)

(** val c_wins : 'a1 list -> ('a1 -> 'a1 -> z) -> 'a1 -> bool **)

let c_wins dec_cand cand_all0 marg nt c =
   forallb (fun d ->
       Z.leb (linear_search dec_cand d c marg nt)
             (linear_search dec_cand c d marg nt)) cand_all0
  (*
  forallb (fun d ->
    Z.leb (m dec_cand cand_all0 marg (length cand_all0) d c)
      (m dec_cand cand_all0 marg (length cand_all0) c d)) cand_all0 *)

(** val iterated_marg_wins_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
    wins_type **)

let iterated_marg_wins_type cand_all0 dec_cand marg nt c d =
  let s = linear_search dec_cand c d marg nt  in 
  (* m dec_cand cand_all0 marg (length cand_all0) c d *)
  ExistT (s,
  (let hi =
     iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s c d nt
   in
   Pair (hi,
         (let r = linear_search dec_cand d c marg nt (* m dec_cand cand_all0 marg (length cand_all0) d c *) in
    ExistT ((fun x ->
             Z.leb (linear_search dec_cand (fst x) (snd x) marg nt (*m dec_cand cand_all0 marg (length cand_all0) (fst x) (snd x) *)) r), __)))))

(** val exists_fin_reify : ('a1 -> sumbool) -> 'a1 list -> ('a1, __) sigT **)

let rec exists_fin_reify pdec = function
| Nil -> assert false (* absurd case *)
| Cons (h, t) ->
  (match pdec h with
   | Left -> ExistT (h, __)
   | Right -> exists_fin_reify pdec t)

(** val reify_opponent :
    'a1 list -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1, __) sigT **)

let reify_opponent dec_cand cand_all0 marg nt c =
  let hdec = fun d ->
    let s =
      z_lt_ge_bool (linear_search dec_cand c d marg nt) (*(m dec_cand cand_all0 marg (length cand_all0) c d) *)
                   (linear_search dec_cand d c marg nt) (*
        (m dec_cand cand_all0 marg (length cand_all0) d c) *)
    in
    (match s with
     | True -> Left
     | False -> Right)
  in
  exists_fin_reify hdec cand_all0

(** val iterated_marg_loses_type :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1
    loses_type **)

let iterated_marg_loses_type cand_all0 dec_cand marg nt c =
  let hE = reify_opponent dec_cand cand_all0 marg nt c in
  let ExistT (d, _) = hE in
  let s = linear_search dec_cand d c marg nt (*m dec_cand cand_all0 marg (length cand_all0) d c*) in
  ExistT (s, (ExistT (d, (Pair
  ((iterated_marg_patht cand_all0 dec_cand marg (length cand_all0) s d c nt),
  (ExistT ((fun x ->
            Z.ltb (linear_search dec_cand (fst x) (snd x) marg nt) (*m dec_cand cand_all0 marg (length cand_all0) (fst x) (snd x))*) s), __)))))))

(** val wins_loses_type_dec :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1
    wins_type, 'a1 loses_type) sum **)

let wins_loses_type_dec cand_all0 dec_cand marg nt c =
  let b = c_wins dec_cand cand_all0 marg nt c in
  (match b with
   | True -> Inl (iterated_marg_wins_type cand_all0 dec_cand marg nt c)
   | False -> Inr (iterated_marg_loses_type cand_all0 dec_cand marg nt c))

type 'cand ballot = 'cand -> nat

type 'cand count =
| Ax of 'cand ballot list * ('cand -> 'cand -> z)
| Cvalid of 'cand ballot * 'cand ballot list * ('cand -> 'cand -> z)
   * ('cand -> 'cand -> z) * 'cand ballot list * 'cand count
| Cinvalid of 'cand ballot * 'cand ballot list * ('cand -> 'cand -> z)
   * 'cand ballot list * 'cand count
| Fin of ('cand -> 'cand -> z) * 'cand ballot list * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand count

(** val forall_exists_fin_dec : 'a1 list -> ('a1 -> nat) -> sumbool **)

let rec forall_exists_fin_dec l f =
  match l with
  | Nil -> Left
  | Cons (h, t) ->
    (match Nat.eq_dec (f h) O with
     | Left -> Right
     | Right -> forall_exists_fin_dec t f)

(** val ballot_valid_dec : 'a1 list -> 'a1 ballot -> sumbool **)

let ballot_valid_dec cand_all0 b =
  forall_exists_fin_dec cand_all0 b

(** val update_marg : 'a1 ballot -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 -> z **)

let update_marg p m0 c d =
  match Nat.ltb (p c) (p d) with
  | True -> Z.add (m0 c d) (Zpos XH)
  | False ->
    (match Nat.ltb (p d) (p c) with
     | True -> Z.sub (m0 c d) (Zpos XH)
     | False -> m0 c d)

(** val listify_v :
    'a1 list -> ('a1 -> 'a1 -> z) -> (('a1, 'a1) prod, z) prod list **)

let listify_v cand_all0 m0 =
  map (fun s -> Pair ((Pair ((fst s), (snd s))), (m0 (fst s) (snd s))))
    (all_pairs cand_all0)

(** val linear_search_v :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 -> ('a1 -> 'a1 -> z) -> (('a1, 'a1)
    prod, z) prod list -> z **)

let rec linear_search_v dec_cand c d m0 = function
| Nil -> m0 c d
| Cons (y, t) ->
  let Pair (y0, k) = y in
  let Pair (c1, c2) = y0 in
  (match dec_cand c c1 with
   | Left ->
     (match dec_cand d c2 with
      | Left -> k
      | Right -> linear_search_v dec_cand c d m0 t)
   | Right -> linear_search_v dec_cand c d m0 t)

(** val update_marg_listify :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot -> ('a1 -> 'a1 -> z) ->
    'a1 -> 'a1 -> z **)

let update_marg_listify cand_all0 dec_cand p m0 =
  let t = update_marg p m0 in
  let l = listify_v cand_all0 t in
  (fun c d -> linear_search_v dec_cand c d t l)

(** val partial_count_all_counted :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot list -> 'a1 ballot list
    -> 'a1 ballot list -> ('a1 -> 'a1 -> z) -> 'a1 count -> ('a1 ballot list,
    ('a1 -> 'a1 -> z, 'a1 count) sigT) sigT **)

let rec partial_count_all_counted cand_all0 dec_cand bs u inbs m0 hc =
  match u with
  | Nil -> ExistT (inbs, (ExistT (m0, hc)))
  | Cons (h, t) ->
    (match ballot_valid_dec cand_all0 h with
     | Left ->
       let w = update_marg_listify cand_all0 dec_cand h m0 in
       partial_count_all_counted cand_all0 dec_cand bs t inbs w (Cvalid (h,
         t, m0, w, inbs, hc))
     | Right ->
       partial_count_all_counted cand_all0 dec_cand bs t (Cons (h, inbs)) m0
         (Cinvalid (h, t, m0, inbs, hc)))

(** val all_ballots_counted :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot list -> ('a1 ballot
    list, ('a1 -> 'a1 -> z, 'a1 count) sigT) sigT **)

let all_ballots_counted cand_all0 dec_cand bs =
  partial_count_all_counted cand_all0 dec_cand bs bs Nil (fun _ _ -> Z0) (Ax
    (bs, (fun _ _ -> Z0)))

(** val schulze_winners :
    'a1 list -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot list -> ('a1 -> bool,
    ('a1 count, __) sigT) sigT **)

         

let schulze_winners cand_all0 dec_cand bs =
  let ExistT (i, t) = all_ballots_counted cand_all0 dec_cand bs in
  let ExistT (m0, p) = t in
  let tt = listify cand_all0 m0 in
  let nt = mm cand_all0 dec_cand m0 (length cand_all0) tt in 
  ExistT ((c_wins dec_cand cand_all0 m0 nt), (ExistT ((Fin (m0, i,
                                                             (c_wins dec_cand cand_all0 m0 nt),
  (wins_loses_type_dec cand_all0 dec_cand m0 nt), p)), __)))

type cand =
| A
| B
| C
| D
| E
| F
| G
| H
| I
| J
| K
| L
| N
| P
| Q
| R
| T
| U
| V
| W
| X
| Y
| Z
(** val cand_all : cand list **)

let cand_all =
  Cons (A, (Cons (B, (Cons (C, (Cons (D, Cons (E, Cons (F, Cons (G, Cons (H, Cons (I, Cons (J, Cons (K, Cons (L, Cons (N, Cons (P, Cons (Q, Cons (R, Cons (T, Cons (U, Cons (V, Cons (X, Cons (Y, Cons (Z, Nil)))))))))))))))))))))))))
                                                                                                                                                                                               

(** val cand_eq_dec : cand -> cand -> sumbool **)

let cand_eq_dec a b =
  match a with
  | A ->
    (match b with
     | A -> Left
     | _ -> Right)
  | B ->
    (match b with
     | B -> Left
     | _ -> Right)
  | C ->
    (match b with
     | C -> Left
     | _ -> Right)
  | D ->
    (match b with
     | D -> Left
     | _ -> Right)
  | E ->
      (match b with
       | E -> Left
       | _ -> Right)
  | F ->
      (match b with
       | F -> Left
       | _ -> Right)
  | G ->
      (match b with
       | G -> Left
       | _ -> Right)
  | H ->
      (match b with
       | H -> Left
       | _ -> Right)
  | I ->
      (match b with
       | I -> Left
       | _ -> Right)
  | J ->
    (match b with
     | J -> Left
     | _ -> Right)
  | K ->
    (match b with
     | K -> Left
     | _ -> Right)
  | L ->
    (match b with
     | L -> Left
     | _ -> Right)
  | N ->
    (match b with
     | N -> Left
     | _ -> Right)
  | P ->
      (match b with
       | P -> Left
       | _ -> Right)
  | Q ->
      (match b with
       | Q -> Left
       | _ -> Right)
  | R ->
      (match b with
       | R -> Left
       | _ -> Right)
  | T ->
      (match b with
       | T -> Left
       | _ -> Right)
  | U ->
      (match b with
       | U -> Left
       | _ -> Right)
  | V ->
      (match b with
       | V -> Left
       | _ -> Right)
  | W ->
      (match b with
       | W -> Left
       | _ -> Right)
  | X ->
      (match b with
       | X -> Left
       | _ -> Right)
  | Y ->
      (match b with
       | Y -> Left
       | _ -> Right)
  | Z ->
      (match b with
       | Z -> Left
       | _ -> Right)

(** val schulze_winners_pf :
    cand ballot list -> (cand -> bool, (cand count, __) sigT) sigT **)

let schulze_winners_pf =
  schulze_winners cand_all cand_eq_dec
