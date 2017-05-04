type __ = Obj.t

type bool =
| True
| False
[@@deriving show]

type nat =
| O
| S of nat
[@@deriving show]
         
type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b
[@@deriving show]
           
type ('a, 'b) prod =
| Pair of 'a * 'b
[@@deriving show]                   

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a coqlist =
| Nil
| Cons of 'a * 'a coqlist
[@@deriving show]
                  
val length : 'a1 coqlist -> nat

type comparison =
| Eq
| Lt
| Gt
[@@deriving show]

val compOpp : comparison -> comparison

type 'a sig0 =
  'a
[@@deriving show]    
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p
[@@deriving show]
                   
type sumbool =
| Left
| Right
[@@deriving show]

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val eq_dec : nat -> nat -> sumbool
 end

type positive =
| XI of positive
| XO of positive
| XH
[@@deriving show]

type z =
| Z0
| Zpos of positive
| Zneg of positive
[@@deriving show]
            
module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

val map : ('a1 -> 'a2) -> 'a1 coqlist -> 'a2 coqlist

val forallb : ('a1 -> bool) -> 'a1 coqlist -> bool

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z
 end

val bool_of_sumbool : sumbool -> bool

val z_lt_dec : z -> z -> sumbool

val z_ge_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_ge_lt_dec : z -> z -> sumbool

val z_lt_ge_bool : z -> z -> bool

val maxlist : z coqlist -> z

val max_of_nonempty_list_type :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> z -> ('a1 -> z) -> ('a1, __) sigT

type 'cand pathT =
| UnitT of 'cand * 'cand
| ConsT of 'cand * 'cand * 'cand * 'cand pathT
[@@deriving show]
                                         
type 'cand wins_type = 'cand -> (z, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod) sigT

type 'cand loses_type =
  (z, ('cand, ('cand pathT, (('cand, 'cand) prod -> bool, __) sigT) prod) sigT) sigT

val m : 'a1 coqlist -> ('a1 -> 'a1 -> z) -> nat -> 'a1 -> 'a1 -> z

val iterated_marg_patht :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> nat -> z -> 'a1 -> 'a1 -> 'a1 pathT

val c_wins : 'a1 coqlist -> ('a1 -> 'a1 -> z) -> 'a1 -> bool

val iterated_marg_wins_type :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 wins_type

val exists_fin_reify : ('a1 -> sumbool) -> 'a1 coqlist -> ('a1, __) sigT

val reify_opponent : 'a1 coqlist -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1, __) sigT

val iterated_marg_loses_type :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 loses_type

val wins_loses_type_dec :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> ('a1 -> 'a1 -> z) -> 'a1 -> ('a1 wins_type, 'a1 loses_type)
  sum

type 'cand ballot = 'cand -> nat

type 'cand count =
| Ax of 'cand ballot coqlist * ('cand -> 'cand -> z)
| Cvalid of 'cand ballot * 'cand ballot coqlist * ('cand -> 'cand -> z) * ('cand -> 'cand -> z)
   * 'cand ballot coqlist * 'cand count
| Cinvalid of 'cand ballot * 'cand ballot coqlist * ('cand -> 'cand -> z) * 'cand ballot coqlist
   * 'cand count
| Fin of ('cand -> 'cand -> z) * 'cand ballot coqlist * ('cand -> bool)
   * ('cand -> ('cand wins_type, 'cand loses_type) sum) * 'cand count
[@@deriving show]
                                                                
val forall_exists_fin_dec : 'a1 coqlist -> ('a1 -> nat) -> sumbool

val ballot_valid_dec : 'a1 coqlist -> 'a1 ballot -> sumbool

val update_marg : 'a1 ballot -> ('a1 -> 'a1 -> z) -> 'a1 -> 'a1 -> z

val partial_count_all_counted :
  'a1 coqlist -> 'a1 ballot coqlist -> 'a1 ballot coqlist -> 'a1 ballot coqlist -> ('a1 -> 'a1 -> z) -> 'a1 count
  -> ('a1 ballot coqlist, ('a1 -> 'a1 -> z, 'a1 count) sigT) sigT

val all_ballots_counted :
  'a1 coqlist -> 'a1 ballot coqlist -> ('a1 ballot coqlist, ('a1 -> 'a1 -> z, 'a1 count) sigT) sigT

val schulze_winners :
  'a1 coqlist -> ('a1 -> 'a1 -> sumbool) -> 'a1 ballot coqlist -> ('a1 -> bool, ('a1 count, __) sigT) sigT

type cand =
| A
| B
| C
| D
[@@deriving show]

val cand_all : cand coqlist

val cand_eq_dec : cand -> cand -> sumbool

val schulze_winners_pf : cand ballot coqlist -> (cand -> bool, (cand count, __) sigT) sigT

val schulze_margin_pf : cand ballot coqlist ->
                        (cand ballot coqlist, (cand -> cand -> z, cand count) sigT) sigT
