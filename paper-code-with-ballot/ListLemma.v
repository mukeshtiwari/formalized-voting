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

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

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

Lemma Zminmax : forall m n s, Z.min m n >= s <-> m >= s /\ n >= s.
Proof.
  split; intros. unfold Z.min in H.
  destruct (m ?= n) eqn:Ht.
  pose proof (proj1 (Z.compare_eq_iff _ _) Ht). intuition.
  pose proof (proj1 (Z.compare_lt_iff _ _) Ht). intuition.
  pose proof (proj1 (Z.compare_gt_iff _ _) Ht). intuition.
  destruct H as [H1 H2].
  unfold Z.min. destruct (m ?= n) eqn:Ht; auto.
Qed.

Lemma exists_list : forall (A : Type) (l : list A) (n : nat),
    (length l >= S n)%nat -> exists a ls, l = a :: ls.
Proof.
  intros A l. destruct l eqn: Ht; intros; simpl in H. inversion H.
  exists a, l0. reflexivity.
Qed.

Lemma in_notin_exist : forall (A : Type) (a x : A) (l : list A),
    In a l -> ~ In x l -> x <> a.
Proof.
  intros A a x l H1 H2.
  induction l. inversion H1.
  specialize (proj1 (not_in_cons x a0 l) H2); intros.
  simpl in H1. destruct H as [H3 H4]. destruct H1.
  subst. assumption. apply IHl. assumption. assumption.
Qed.

Definition covers (A : Type) (c l : list A) := forall x : A, In x l -> In x c.

Lemma list_finite_elem : forall (A : Type) (n : nat) (c : list A) (H1 : forall x y : A, {x = y} + {x <> y}),
    length c = n -> forall (l : list A) (H : (length l > length c)%nat),
      covers A c l -> exists (a : A) l1 l2 l3, l = l1 ++ (a :: l2) ++ (a :: l3).
Proof.
  intros A n. induction n; intros. unfold covers in H1. rewrite H in H0.
  unfold covers in H2. pose proof (proj1 (length_zero_iff_nil c) H).
  rewrite H3 in H2. simpl in H2. pose proof (exists_list _ _ _ H0).
  destruct H4 as [a [ls H4]]. rewrite H4 in H2. specialize (H2 a (in_eq a ls)). inversion H2.  
  rewrite H in H0. pose proof (exists_list _ _ _ H0).
  destruct H3 as [l0 [ls H3]].
  pose proof (in_dec H1 l0 ls). destruct H4.
  pose proof (in_split l0 ls i). destruct H4 as [l1 [l2 H4]].
  rewrite H4 in H3. exists l0, [], l1, l2. simpl. auto.
  unfold covers in H2. rewrite H3 in H2.
  pose proof (H2 l0 (in_eq l0 ls)).
  pose proof (in_split l0 c H4). destruct H5 as [l1 [l2 H5]].
  rewrite H5 in H. rewrite app_length in H. simpl in H.
  assert (Ht : (length l1 + S (length l2))%nat = (S (length l1 + length l2))%nat) by omega.
  rewrite Ht in H. clear Ht. inversion H. clear H.
  rewrite <- app_length in H7.
  assert ((length ls > length (l1 ++ l2))%nat).
  { rewrite H7. rewrite H3 in H0. simpl in H0. omega. }
  specialize (IHn (l1 ++ l2) H1 H7 ls H).  
  assert (covers A (l1 ++ l2) ls).
  { unfold covers. intros x Hin.
    specialize (in_notin_exist _ x l0 ls Hin n0); intros.
    specialize (H2 x (or_intror Hin)).
    rewrite H5 in H2.
    pose proof (in_app_or l1 (l0 :: l2) x H2). destruct H8.
    apply in_or_app. left. assumption.
    simpl in H8. destruct H8. contradiction.
    apply in_or_app. right. assumption. }
  specialize (IHn H6). destruct IHn as [a [l11 [l22 [l33 H10]]]].
  exists a, (l0 :: l11), l22, l33.  simpl. rewrite H10 in H3. assumption.
Qed.

Lemma Zmaxlemma : forall m n s, Z.max m n >= s <-> m >= s \/ n >= s.
Proof.
  split; intros. unfold Z.max in H. destruct (m ?= n) eqn : Ht.
  left. auto. right. auto. left. auto.
  destruct H. unfold Z.max. destruct (m ?= n) eqn: Ht.
  auto. pose proof (proj1 (Z.compare_lt_iff _ _) Ht). omega. omega.
  unfold Z.max. destruct (m ?= n) eqn:Ht.
  pose proof (proj1 (Z.compare_eq_iff _ _) Ht). omega.
  omega. pose proof (proj1 (Z.compare_gt_iff _ _) Ht). omega.
Qed.

Lemma list_and_num : forall (A : Type) (n : nat) (l : list A),
    (length l > n)%nat -> exists p, (length l = p + n)%nat.
Proof.
  intros A n l H. induction l. inversion H.
  simpl in *. apply gt_S in H. destruct H. specialize (IHl H). destruct IHl as [p IHl].
  exists (S p). omega. exists 1%nat. omega.
Qed.

Lemma forallb_false : forall (A : Type) (f : A -> bool) (l : list A), 
    forallb f l = false <-> (exists x, In x l /\ f x = false).
Proof.
  intros A f l. split. intros H. induction l. simpl in H. inversion H.
  simpl in H. apply andb_false_iff in H. destruct H.
  exists a. split. simpl. left. auto. assumption.
  pose proof IHl H. destruct H0. exists x. destruct  H0 as [H1 H2].
  split. simpl. right. assumption. assumption.  
  intros. destruct H as [x [H1 H2]]. induction l. inversion H1.
  simpl. apply andb_false_iff. simpl in H1. destruct H1.
  left. congruence. right. apply IHl. assumption.
Qed.

(* this proof is same as first half of Max_of_nonempty_list. Type level existance *)
Lemma L9 : forall (A : Type) (l : list A) (H : l <> nil)
             (H1 : forall x y : A, {x = y} + {x <> y}) (s : Z) (f : A -> Z),
    maxlist (map f l) >= s -> existsT (x:A), In x l /\ f x >= s.
Proof.
  induction l; intros. specialize (H eq_refl). inversion H.
  pose proof (list_eq_dec H1 l []). destruct H2.
  exists a. subst. intuition.
  assert (Hm : {f a >= maxlist (map f l)} + {f a < maxlist (map f l)}) by
      apply (Z_ge_lt_dec (f a) (maxlist (map f l))).
  destruct Hm. rewrite map_cons in H0. pose proof (exists_last n).
  destruct X as [l1 [x l2]].
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
  specialize (IHl n H1 s f H0). destruct IHl. exists x0. intuition.
Defined.

Lemma L11 : forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false -> existsT x, In x l /\ f x = false.
Proof.
  intros A f. induction l. simpl. intros. inversion H.
  simpl. intros. destruct (f a) eqn:H1. destruct (forallb f l) eqn:H2.
  inversion H. specialize (IHl eq_refl). clear H.
  destruct IHl as [x [H3 H4]].
  exists x. split. right. auto. assumption.
  destruct (forallb f l) eqn:H2. exists a. split. left. auto. assumption.
  clear H. specialize (IHl eq_refl). destruct IHl as [x [H3 H4]].
  exists x. split. right. assumption. assumption.
Qed.

(* End of List Lemma file *)
