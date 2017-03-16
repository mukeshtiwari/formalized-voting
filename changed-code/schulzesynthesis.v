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

  (* losing condition in Schuze counting *)
  Definition loses_prop (c : cand) :=
    exists k d, Path k d c /\ (forall l, Path l c d -> l < k).
  
  Definition loses_type (c : cand) :=
    existsT (k : Z) (d : cand),
    ((PathT k d c) *
     (existsT (f : (cand * cand) -> bool),
      f (c, d) = true /\ coclosed k f))%type.

  (* type-level paths allow to construct evidence for the existence of paths *)
  Lemma path_equivalence : forall c d k , PathT k c d -> Path k c d.
  Proof.
    intros c d k H.
    induction H; [constructor 1 | constructor 2 with d]; auto.
  Qed.

  
  Lemma mp_log : forall k p f,
      mp k p f = true -> forall b, f (b, snd p) = true \/ edge (fst p) b < k.
  Proof.
    intros k p f H b.
    assert (Hin : In b cand_all) by  apply cand_fin.
    assert (Hp : In b cand_all -> (mpf k p f) b = true) by (apply forallb_forall; auto).
    specialize (Hp Hin); apply orb_true_iff in Hp; destruct Hp as [Hpl | Hpr];
      destruct p as (a, c); simpl in *.
    + right; apply Zlt_is_lt_bool; auto.
    + left; auto.
  Qed.

  Lemma coclosed_path : forall k f, coclosed k f -> forall s x y,
        Path s x y -> f (x, y) = true -> s < k.
  Proof.
    intros k f Hcc x s y p.
    induction p.
    (* unit path *)
    + intros Hin; specialize (Hcc (c, d) Hin); apply andb_true_iff in Hcc;
        destruct Hcc as [Hccl Hccr]; apply Zlt_is_lt_bool in Hccl; simpl in Hccl;  omega.
    (* non unit path *)
    + intros Hin; specialize (Hcc (c, e) Hin); apply andb_true_iff in Hcc;
        destruct Hcc as [Hccl Hccr]; unfold el in Hccl; simpl in Hccl.
      assert (Hmp : forall m, f (m, (snd (c, e))) = true \/ edge (fst (c, e)) m < k)
        by (apply mp_log; auto); simpl in Hmp.
      specialize (Hmp d).
      destruct Hmp; [intuition | omega].
  Qed.

  (* elg is boolean function returns true if the edge between two candidates of >= k. *)
  Definition elg (k : Z) (p : (cand * cand)) : bool :=
    Zge_bool (edge (fst p) (snd p)) k.

  (* mp k (a, c) f (for midpoint) returns true if there's a midpoint b st.
     the edge between a and b is >= k /\ the function f (b, c) = true *)
  Definition mpg (k : Z) (p : (cand * cand)) (f : (cand * cand) -> bool) :=
    let a := fst p in
    let c := snd p in
    existsb (fun b => andb (elg k (a, b)) (f (b, c))) cand_all.

  
  (* Now adding Matrix code and removing fixpoint code *)

  Fixpoint maxlist (l : list Z) : Z :=
    match l with
    | [] => 0%Z
    | [h] => h
    | h :: t => Z.max h (maxlist t)
    end.
  
  
  (* the function M n maps a pair of candidates c, d to the strength of the strongest path of 
     length at most (n + 1) *)
  Fixpoint M (n : nat) (c d : cand) : Z :=
    match n with
    | 0%nat => edge c d 
    | S n' =>
      Z.max (M n' c d)
            (maxlist (map (fun x : cand => Z.min (edge c x) (M n' x d)) cand_all))
    end.

  
