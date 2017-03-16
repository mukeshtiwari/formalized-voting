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
    {
      destruct l1. simpl in l2. rewrite l2. simpl. auto.
      rewrite l2. simpl. auto.
    }    
    pose proof (Z.ge_le _ _ g). pose proof (Z.max_l _ _ H3).
    rewrite H2 in H0. rewrite H4 in H0. exists a. intuition.
    rewrite map_cons in H0. pose proof (exists_last n). destruct X as [l1 [x l2]].
    assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
    {
      destruct l1. simpl in l2. rewrite l2. simpl. auto.
      rewrite l2. simpl. auto.
    }    
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
    {    
      destruct l1. simpl in H4. rewrite H4. simpl. auto.
      rewrite H4. simpl. auto.
    }    
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
    subst.  assumption. apply IHl. assumption. assumption.
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
    unfold covers in H2.
    rewrite H3 in H2.
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
    {
      unfold covers. intros x Hin.
      specialize (in_notin_exist _ x l0 ls Hin n0); intros.
      specialize (H2 x (or_intror Hin)).
      rewrite H5 in H2.
      pose proof (in_app_or l1 (l0 :: l2) x H2). destruct H8.
      apply in_or_app. left. assumption.
      simpl in H8. destruct H8. contradiction.
      apply in_or_app. right. assumption.
    }
    specialize (IHn H6). destruct IHn as [a [l11 [l22 [l33 H10]]]].
    exists a, (l0 :: l11), l22, l33.  simpl. rewrite H10 in H3.
    assumption.
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
  
  (* induction on n *)  
  Lemma L1 : forall (n : nat) (s : Z) (c d : cand),
      M n c d >= s -> Path s c d.
  Proof.
    induction n. simpl. intros.
    constructor. auto.
    intros s c d H. simpl in H.
    pose proof (proj1 (Zmaxlemma (M n c d) _  s) H).
    destruct H0. pose proof (IHn _ _ _ H0). assumption.
    pose proof
         (Max_of_nonempty_list _ cand_all cand_not_nil dec_cand s
                               (fun x : cand => Z.min (edge c x) (M n x d))).
    destruct H1.  clear H2. pose proof (H1 H0).
    destruct H2 as [e H2]. destruct H2.
    pose proof (Zminmax (edge c e) (M n e d) s). destruct H4.
    specialize (H4 H3). destruct H4.
    constructor 2 with (d := e). auto.
    apply IHn. assumption.
  Qed.

  (* induction on path *)
  Lemma L2 : forall (s : Z) (c d : cand),      
      Path s c d -> exists n, M n c d >= s.
  Proof.
    intros s c d H. induction H.
    exists 0%nat. auto. destruct IHPath.
    exists (S x). simpl. apply Zmaxlemma. right.
    apply Max_of_nonempty_list.
    apply cand_not_nil. apply dec_cand. exists d.
    split. pose proof (cand_fin d). auto.
    apply Zminmax. split. auto. auto.
  Qed.

  
  Lemma monotone_M : forall (n m : nat) c d, (n <= m)%nat  -> M n c d <= M m c d.
  Proof.
    intros n m c d H. induction H; simpl; try omega.
    apply Z.ge_le. apply Zmaxlemma with (m := M m c d). 
    left. omega.
  Qed.
  
  Fixpoint str c l d :=
    match l with
    | [] => edge c d
    | (x :: xs) => Z.min (edge c x)  (str x xs d)
    end.

  
