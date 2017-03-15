Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z.
Section Evote. 

  (* type level existential quantifier *)
  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'") : type_scope.

  (* candidates are a finite type with decidable equality *)
  Parameter cand : Type.
  Parameter cand_all : list cand.

  (* edge is the margin in Schulze counting, i.e. edge c d is the number of 
     voters that perfer c over d *)
  Parameter edge : cand -> cand -> Z. 

  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.

  (* prop-level path *)
  Inductive Path (k: Z) : cand -> cand -> Prop :=
  | unit c d : edge c d >= k -> Path k c d
  | cons  c d e : edge c d >= k -> Path k d e -> Path k c e.

  (* type-level path *)
  Inductive PathT (k: Z) : cand -> cand -> Type :=
  | unitT : forall c d, edge c d >= k -> PathT k c d
  | consT : forall c d e, edge c d >= k -> PathT k d e -> PathT k c e.



  (* auxilary functions: all pairs that can be formed from a list *)
  Fixpoint all_pairs {A: Type} (l: list A): list (A * A) :=
    match l with
    | [] => []
    | c::cs => (c, c) :: (all_pairs cs)
                     ++  (map (fun x => (c, x)) cs) 
                     ++ (map (fun x => (x, c)) cs)
    end.

  (* boolean equality on candidates derived from decidable equality *)
  Definition cand_eqb (c d: cand) := proj1_sig (bool_of_sumbool (dec_cand c d)).

  (* boolean equality is equality *)
  Lemma cand_eqb_prop (c d: cand) : cand_eqb c d = true -> c = d.
  Proof.
    unfold cand_eqb; intros. destruct (dec_cand c d); [assumption | inversion H].
  Qed.

  
  (* definition of < k *)
  Definition el (k : Z) (p : (cand * cand)) :=
    Zlt_bool (edge (fst p) (snd p)) k.

  Definition mpf (k : Z) (p : (cand * cand)%type) (f : (cand * cand) -> bool) (b : cand) :=
    let a := fst p in
    let c := snd p in
    (el k (a, b) || f (b, c)).

  Definition mp (k : Z) (p : (cand * cand)%type) (f : (cand * cand) -> bool) :=
    forallb (mpf k p f) cand_all.

  Definition W (k : Z) := fun f => (fun p => andb (el k p) (mp k p f)).

   Definition coclosed (k : Z) (f : (cand * cand) -> bool) :=
     forall x, f x = true -> W k f x = true.

  
  (* winning condition in Schulze counting *)
  Definition wins_prop (c: cand) :=
    forall d : cand, exists k : Z, 
        ((Path k c d) /\ (forall l, Path l d c -> l <= k)).

  Definition wins_type c :=
    forall d : cand, existsT (k : Z),
    ((PathT k c d) *
     (existsT (f : (cand * cand) -> bool),
      f (d, c) = true /\ coclosed (k + 1) f))%type.

  
  
