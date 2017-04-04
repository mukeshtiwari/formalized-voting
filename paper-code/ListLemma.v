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

Fixpoint all_pairs {A: Type} (l: list A): list (A * A) :=
  match l with
  | [] => []
  | c::cs => (c, c) :: (all_pairs cs)
                   ++  (map (fun x => (c, x)) cs) 
                   ++ (map (fun x => (x, c)) cs)
  end.

Fixpoint maxlist (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | [h] => h
  | h :: t => Z.max h (maxlist t)
  end.

Lemma Zmn_lt : forall (m n : Z), m < n -> Z.max m n = n.
Proof.
  intros m n H; apply Z.max_r; omega.
Qed.

Lemma Max_of_nonempty_list :
  forall (A : Type) (l : list A) (H : l <> nil) (H1 : forall x y : A, {x = y} + {x <> y}) (s : Z) (f : A -> Z),
    maxlist (map f l) >= s <-> exists (x:A), In x l /\ f x >= s.
Proof.
  split; intros. generalize dependent l.
  induction l; intros. specialize (H eq_refl). inversion H.
  pose proof (list_eq_dec H1 l []).
  destruct H2. exists a. rewrite e. intuition. rewrite e in H0.
  simpl in H0. auto.
  assert (Hm : {f a >= maxlist (map f l)} + {f a < maxlist (map f l)}) by
      apply (Z_ge_lt_dec (f a) (maxlist (map f l))).
  destruct Hm. rewrite map_cons in H0.
  pose proof (exists_last n).  destruct X as [l1 [x l2]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in l2. rewrite l2. simpl. auto.
    rewrite l2. simpl. auto. }
  pose proof (Z.ge_le _ _ g). pose proof (Z.max_l _ _ H3).
  rewrite H2 in H0. rewrite H4 in H0. exists a. intuition.
  rewrite map_cons in H0. pose proof (exists_last n). destruct X as [l1 [x l2]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in l2. rewrite l2. simpl. auto.
    rewrite l2. simpl. auto. }    
  rewrite H2 in H0. pose proof (Zmn_lt _ _ l0). rewrite H3 in H0.
  specialize (IHl n H0). destruct IHl. exists x0. intuition.
  destruct H0 as [x [H2 H3]].
  induction l. specialize (H eq_refl). inversion H.
  pose proof (list_eq_dec H1 l []). destruct H0.
  (* empty list *)
  subst. simpl in *. destruct H2. subst. auto. inversion H0.
  (* not empty list *)
  rewrite map_cons. pose proof (exists_last n). destruct X as [l1 [x0 H4]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in H4. rewrite H4. simpl. auto.
    rewrite H4. simpl. auto. }    
  rewrite H0. unfold Z.max. destruct (f a ?= maxlist (map f l)) eqn:Ht.
  destruct H2. subst. auto. pose proof (proj1 (Z.compare_eq_iff _ _) Ht).
  specialize (IHl n H2). rewrite H5. auto.
  destruct H2. subst.
  pose proof (proj1 (Z.compare_lt_iff _ _) Ht). omega.
  apply IHl. assumption. assumption.
  destruct H2. subst. assumption. specialize (IHl n H2).
  pose proof (proj1 (Z.compare_gt_iff _ _) Ht).  omega.
Qed.

