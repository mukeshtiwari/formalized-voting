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
     format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'") : type_scope.

Section ListLemma.
   
    (* auxilary functions: all pairs that can be formed from a list *)
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
  
  
  (* this proof is same as first half of Max_of_nonempty_list *)
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

End ListLemma.

Section Evote. 

  (* candidates are a finite type with decidable equality *)
  Parameter cand : Type.
  Parameter cand_all : list cand.

  (* edge is the margin in Schulze counting, i.e. edge c d is the number of 
     voters that perfer c over d *)
  Variable edge : cand -> cand -> Z. 

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

  
  (* Now adding Matrix code and removing fixpoint code *)
  
  (* the function M n maps a pair of candidates c, d to the strength of the strongest path of 
     length at most (n + 1) *)
  Fixpoint M (n : nat) (c d : cand) : Z :=
    match n with
    | 0%nat => edge c d 
    | S n' =>
      Z.max (M n' c d)
            (maxlist (map (fun x : cand => Z.min (edge c x) (M n' x d)) cand_all))
    end.
  
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

  Lemma path_len : forall k c d s l,
      (length l <= k)%nat -> str c l d >= s -> M k c d >= s.
  Proof.
    induction k. intros. assert ((length l <= 0)%nat -> l = []).
    {
      destruct l. intros. reflexivity.
      simpl in *. inversion H.
    }
    specialize (H1 H). subst. simpl in *. auto.
    intros. simpl in *.
    destruct l. simpl in *. apply Zmaxlemma.
    left. apply IHk with []. simpl. omega. simpl. auto.
    simpl in *. apply Zminmax in H0. destruct H0.
    apply Zmaxlemma. right. apply Max_of_nonempty_list.
    apply cand_not_nil. apply dec_cand. exists c0. split. specialize (cand_fin c0). assumption.
    apply Zminmax. split.
    omega. apply IHk with l. omega. omega.
  Qed.

  
  Lemma path_length : forall k c d s,
      M k c d >= s <-> exists (l : list cand), (length l <= k)%nat /\ str c l d >= s. 
  Proof.  
    split. generalize dependent s. generalize dependent d.
    generalize dependent c.
    induction k. simpl. intros. exists []. simpl. intuition.

    simpl. intros.
    pose proof (proj1 (Zmaxlemma (M k c d) _ s) H). destruct H0.
    specialize (IHk c d s H0). destruct IHk as [l [H1 H2]]. exists l. omega.
    clear H.
    pose proof
         (Max_of_nonempty_list _ cand_all cand_not_nil dec_cand s
                               (fun x : cand => Z.min (edge c x) (M k x d))).
    
    destruct H. clear H1. specialize (H H0). destruct H as [e [H1 H2]].
    pose proof (proj1 (Zminmax _ _ s) H2). destruct H.
    specialize (IHk e d s H3). destruct IHk as [l [H4 H5]].
    exists (e :: l). simpl. split. omega.
    apply Zminmax. intuition.

    (* otherway *)
    intros. destruct H as [l [H1 H2]].
    pose proof (path_len k c d s l H1 H2). omega.    
  Qed.

  Lemma str_aux : forall c d a l1 l2 s,
      str c (l1 ++ a :: l2) d >= s <-> str c l1 a >= s /\ str a l2 d >= s.
  Proof.
    split. generalize dependent s. generalize dependent l2.
    generalize dependent a. generalize dependent d. generalize dependent c.
    induction l1; simpl; intros.
    apply Zminmax in H. auto. apply Zminmax in H. destruct H.
    assert ((edge c a) >= s /\ (str a l1 a0) >= s /\ str a0 l2 d >= s ->
            Z.min (edge c a) (str a l1 a0) >= s /\ str a0 l2 d >= s).
    {
      intros. destruct H1 as [H1 [H2 H3]]. split. apply Zminmax. auto. auto.
    }
    apply H1. split. assumption.
    apply IHl1. assumption.

    (* other part *)
    generalize dependent s. generalize dependent l2.
    generalize dependent a. generalize dependent d. generalize dependent c.
    induction l1; simpl; intros. apply Zminmax. auto.
    apply Zminmax. destruct H. apply Zminmax in H. destruct H.
    split. auto. apply IHl1. auto.
  Qed.

  
  Lemma str_lemma_1 : forall c d a l l1 l2 l3 s, l = l1 ++ a :: l2 ++ a :: l3 ->
    str c l d >= s -> str c (l1 ++ a :: l3) d >= s.
  Proof.
   intros. subst. apply str_aux in H0. destruct H0.
   apply str_aux in H0. destruct H0.
   pose proof (proj2 (str_aux c d a l1 l3 s) (conj H H1)). auto.
  Qed.

  Lemma str_lemma_2 : forall c d a l l1 l2 l3 s,
      l = l1 ++ a :: l2 ++ a :: l3 -> str c (l1 ++ a :: l3) d >= s -> str a l2 a >= s ->
      str c (l1 ++ a :: l2 ++ a :: l3) d >= s.
  Proof.
    intros. apply str_aux in H0. destruct H0.
    apply str_aux. split. auto.
    apply str_aux. auto.
  Qed.



  Lemma L3 : forall k n c d (Hn: (length cand_all = n)%nat),
      M (k + n) c d <= M n  c d.
  Proof.
    induction k using (well_founded_induction lt_wf). intros n c d Hn.
    remember (M (k + n) c d) as s.
    pose proof (Z.eq_le_incl _ _ Heqs). apply Z.le_ge in H0.
    pose proof (proj1 (path_length _ _ _ _) H0). destruct H1 as [l [H1 H2]].
    (* number of candidates <= length Evote.cand_all \/ > length Evote.cand_all *)
    assert ((length l <= n)%nat \/ (length l > n)%nat) by omega.
    destruct H3 as [H3 | H3].
    pose proof (proj2 (path_length n c d s)
                      (ex_intro (fun l => (length l <= n)%nat /\ str c l d >= s) l (conj H3 H2))).
    omega.

    (* length l > length Evote.cand_all and there are candidates. Remove the duplicate
       candidate *)
    rewrite <- Hn in H3. assert (covers cand cand_all l).
    {
      unfold covers. intros. pose proof (cand_fin x). assumption.
    }
    pose proof (list_finite_elem _ n cand_all dec_cand Hn l H3 H4).
    destruct H5 as [a [l1 [l2 [l3 H5]]]].
    pose proof (str_lemma_1 _ _ _ _ _ _ _ _ H5 H2).
    remember (l1 ++ a :: l3) as l0.
    assert ((length l0 <= n)%nat \/ (length l0 > n)%nat) by omega.
    destruct H7.
    pose proof (path_length n c d s). destruct H8.
    assert ((exists l : list cand, (length l <= n)%nat /\ str c l d >= s)).
    exists l0. intuition. specialize (H9 H10).  omega.   
    
    rewrite Hn in H3.
    specialize (list_and_num _ _ _ H3); intros. destruct H8 as [p H8].
    specialize (list_and_num _ _ _ H7); intros. destruct H9 as [k' H9].
    assert ((length l0 < length l)%nat).
    {
      rewrite Heql0, H5.
      rewrite app_length. rewrite app_length.
      simpl. rewrite app_length. simpl.
      omega.
    }    
    rewrite H9 in H10. rewrite H8 in H10.
    assert (((k' + n) < (p + n))%nat -> (k' < p)%nat) by omega.
    specialize (H11 H10). assert (k' < k)%nat by omega.
    specialize (H k' H12 n c d Hn).
    pose proof (path_length (length l0) c d (str c l0 d)).
    destruct H13.
    assert ((exists l : list cand, (length l <= length l0)%nat /\ str c l d >= str c l0 d)).
    {
      exists l0. omega.
    }
    specialize (H14 H15). clear H13. rewrite <- H9 in H. omega.
  Qed.

  Lemma L4 : forall (c d : cand) (n : nat),
      M n c d <= M (length cand_all) c d. 
  Proof.
    intros c d n. assert ((n <= (length cand_all))%nat \/
                          (n >= (length cand_all))%nat) by omega.
    destruct H. apply monotone_M. assumption.
    remember ((length cand_all)) as v.
    assert ((n >= v)%nat -> exists p, (n = p + v)%nat).
    {
      intros. induction H. exists 0%nat. omega.
      assert ((v <= m)%nat -> (m >= v)%nat) by omega.
      specialize (H1 H). specialize (IHle H1). destruct IHle as [p H2].
      exists (S p). omega.
    }
      
    specialize (H0 H). destruct H0 as [p H0].
    subst. apply L3. auto.
  Qed.

  Definition c_wins c :=
    forallb (fun d => (M (length cand_all) d c) <=? (M (length cand_all) c d))
            cand_all.

  Lemma L5 (c : cand) :
    c_wins c = true <-> forall d, M (length cand_all) d c <= M (length cand_all) c d. 
  Proof.
    split; intros.
    unfold c_wins in H.
    pose proof
         (proj1 (forallb_forall
                   (fun d : cand => M (length cand_all) d c <=?
                                 M (length cand_all) c d) cand_all) H).
    pose proof (H0 d (cand_fin d)). simpl in H1.
    apply Zle_bool_imp_le. assumption.

    unfold c_wins. apply forallb_forall. intros x Hin.
    pose proof H x. apply Zle_imp_le_bool. assumption.
  Qed.

  Lemma L6 (c : cand) :
    c_wins c = false <-> exists d, M (length cand_all) c d < M (length cand_all) d c.
  Proof.
    split; intros. unfold c_wins in H.
    apply forallb_false in H. destruct H as [x [H1 H2]].
    exists x. apply Z.leb_gt in H2. omega.

    destruct H as [d H]. unfold c_wins. apply forallb_false.
    exists d. split. pose proof (cand_fin d). assumption.
    apply Z.leb_gt. omega.
  Qed.

  Lemma L7 : forall c, {c_wins c = true} + {c_wins c = false}.
  Proof.
    intros c. destruct (c_wins c) eqn:Ht. left. reflexivity.
    right. reflexivity.
  Defined.

  (* this proof is exact copy of L2 *)
  Lemma L8 : forall (s : Z) (c d : cand),
      PathT s c d -> exists n, M n c d >= s.
  Proof.
    intros s c d H.
    induction H. exists 0%nat. auto.
    destruct IHPathT. exists (S x). simpl.
    apply Zmaxlemma. right.
    apply Max_of_nonempty_list. apply cand_not_nil.
    apply dec_cand. exists d. split. pose proof (cand_fin d). auto.
    apply Zminmax. auto.
  Qed.

  Lemma L10 : forall n s c d, M n c d >= s -> PathT s c d.
  Proof.
    induction n; simpl; intros. constructor. auto.
    unfold Z.max in H.
    destruct 
      (M n c d
         ?= maxlist (map (fun x : cand => Z.min (edge c x) (M n x d)) cand_all)).
    apply IHn. assumption.
    apply L9 in H. destruct H as [x [H1 H2]]. apply Zminmax in H2. destruct H2.
    specialize (IHn _ _ _ H0). specialize (consT _ _ _ _ H IHn). auto.
    apply cand_not_nil. apply dec_cand. apply IHn. assumption.
  Defined.
  
  (* winning criteria from prop to type *)
  Lemma L13 (c : cand) : forall d k,
        Path k c d /\ (forall l, Path l d c -> l <= k) ->
        M (length cand_all) d c <= M (length cand_all) c d.
  Proof.
    intros d k [H1 H2].
    remember (M (length cand_all) d c) as s.
    apply Z.eq_le_incl in Heqs.
    apply Z.le_ge in Heqs.
    pose proof (L1 _ _ _ _ Heqs). specialize (H2 s H).
    apply L2 in H1. destruct H1 as [n H1].
    pose proof (L4 c d n). omega.
  Qed.

  Lemma L14 (c : cand) :
    (forall d, exists k, Path k c d /\ (forall l, Path l d c -> l <= k)) ->
    forall d, M (length cand_all) d c <= M (length cand_all) c d.
  Proof.
    intros. specialize (H d). destruct H as [k [H1 H2]]. apply L13 with k.
    intuition.
  Qed.
  
  Lemma L15 (c : cand) : (forall d,
      M (length cand_all) d c <= M (length cand_all) c d) ->
      forall d : cand, existsT (k : Z),
    ((PathT k c d) *
     (existsT (f : (cand * cand) -> bool),
      f (d, c) = true /\ coclosed (k + 1) f))%type.
  Proof.
    intros. specialize (H d). remember (M (length cand_all) d c) as s.
    exists s. apply Z.le_ge in H. apply L10 in H. split. auto.
    exists (fun x => M (length cand_all) (fst x) (snd x) <=? s). simpl in *. split.
    apply Z.leb_le. omega.
  
    unfold coclosed. intros. destruct x as (x, z). simpl in *.
    apply Z.leb_le in H0. unfold W. apply andb_true_iff. split.
    unfold el. simpl. apply Z.ltb_lt.
    assert (edge x z <= s -> edge x z < s + 1) by omega.
    apply H1. clear H1. clear Heqs.
    induction (length cand_all). simpl in *. auto.
    simpl in H0. apply Z.max_lub_iff in H0.
    destruct H0. specialize (IHn H0). auto.
    
    unfold mp. apply forallb_forall. intros y Hy.  unfold mpf. simpl in *.
    apply orb_true_iff. unfold el. simpl.
    assert (edge x y <= s \/ edge x y >= s + 1) by omega.
    destruct H1. left. apply Z.ltb_lt. omega.
    right. apply Z.leb_le.
    assert (M (length cand_all) y z <= s \/ M (length cand_all) y z >= s + 1) by omega.
    destruct H2. auto.
    apply L1 in H2. pose proof (cons _ _ _ _ H1 H2).
    apply L2 in H3. destruct H3 as [n H3].
    pose proof (L4 x z n). omega.
  Defined.

  Lemma wins_prop_type : forall c, wins_prop c -> wins_type c.
  Proof.
    intros c H. unfold wins_prop, wins_type in *.
    apply L15. apply L14. auto.
  Qed.

  Lemma wins_type_prop : forall c, wins_type c -> wins_prop c.
  Proof.
    intros c H. unfold wins_prop, wins_type in *. intros d.
    destruct (H d) as [k [H1 [f [H3 H4]]]].
    exists k. split. apply path_equivalence. auto.
    intros l H5. pose proof (coclosed_path _ _ H4).
    pose proof (H0 l _ _ H5 H3). omega.
  Qed.
  (* end of winning criteria *)

  (* losing using M function *)
  Lemma L16 (c : cand) :
    (exists k d, Path k d c /\ (forall l, Path l c d -> l < k)) ->
    (exists d, M (length cand_all) c d < M (length cand_all) d c).
  Proof.
    intros. destruct H as [k [d [H1 H2]]].
    exists d. remember (M (length cand_all) c d)  as s.
    pose proof (Z.eq_le_incl _ _ Heqs) as H3.
    apply Z.le_ge in H3. apply L1 in H3. specialize (H2 s H3).
    apply L2 in H1. destruct H1 as [n H1].
    pose proof (L4 d c n). omega.
  Qed.
  
  Definition constructive_prop (c d : cand):=
     M (length cand_all) c d < M (length cand_all) d c.

  Lemma constructive_deci_cand : forall (c d : cand),
      {(constructive_prop c d)} + {~(constructive_prop c d)}.
  Proof.
    intros c d. unfold constructive_prop.
    pose proof (Z_lt_ge_bool (M (length cand_all) c d) (M (length cand_all) d c)).
    destruct H. destruct x. left. auto.
    right. apply Zle_not_lt. omega.
  Qed.

  Program Fixpoint f0 a l (H : In a l) : nat :=
    match l with
    | [] => _
    | h :: t =>
      if dec_cand a h then O else S (f0 a t _)
    end.
  Next Obligation.
    destruct H; congruence.
  Defined.
  Next Obligation.
    destruct H.
    - exfalso; now apply H0.
    - assumption.
  Defined.

  Definition f (c : cand) : nat := f0 c cand_all (cand_fin c).

  Program Fixpoint g0 n l (H : (n < length l)%nat) : cand :=
    match l, n with
    | [], _ => _
    | h :: _, O => h
    | _ :: t, S n' => g0 n' t _
    end.
  Next Obligation.
    exfalso; inversion H.
  Defined.
  Next Obligation.
    now apply Lt.lt_S_n.
  Defined.

  Program Definition g (n : nat) : cand :=
    if Compare_dec.le_lt_dec (length cand_all) n then _
    else g0 n cand_all _.
  Next Obligation.
    destruct cand_all.
    - exfalso; now apply cand_not_nil.
    - exact c.
  Defined.
    
  Lemma f0_lt_length (a : cand) (l : list cand) (H : In a l) :
    (f0 a l H < length l)%nat.
  Proof.
    revert a H.
    induction l; intros.
    - inversion H.
    - simpl in *. destruct (dec_cand a0 a).
      + omega.
      + apply Lt.lt_n_S. apply IHl.
  Qed.

  Lemma f_lt_length (a : cand) : (f a < length cand_all)%nat.
  Proof.
    apply f0_lt_length.
  Qed.

  Lemma g0_nth (n : nat) (l : list cand) (H : (n < length l)%nat) (c : cand) :
    g0 n l H = nth n l c.
  Proof.
    revert l H.
    induction n; intros; destruct l.
    - inversion H.
    - reflexivity.
    - inversion H.
    - apply IHn.
  Qed.

  Lemma nth_f0 (a : cand) (l : list cand) (H : In a l) (c : cand) :
    nth (f0 a l H) l c = a.
  Proof.
    induction l.
    - inversion H.
    - simpl. now destruct dec_cand.
  Qed.

  Lemma L17 : forall x, g (f x) = x.
  Proof.
    intros.
    unfold g.
    destruct le_lt_dec.
    - pose proof (f_lt_length x). exfalso; omega.
    - unfold g_obligation_2, f.
      rewrite g0_nth with (c := x).
      apply nth_f0.
  Qed.

  Lemma L18 (c : cand) :
    (exists d, M (length cand_all) c d < M (length cand_all) d c) ->
    (existsT (k : Z) (d : cand),
     ((PathT k d c) *
      (existsT (f : (cand * cand) -> bool),
       f (c, d) = true /\ coclosed k f))%type).
  Proof.
    intros.
    pose proof
         (constructive_indefinite_ground_description
            _ f g L17 (constructive_prop c) (constructive_deci_cand c) H).
    destruct X as [d X]. unfold constructive_prop in X.
    remember (M (length cand_all) c d) as s.
    assert (s + 1 <= M (length cand_all) d c) by omega.
    exists (s + 1), d. split. apply Z.le_ge in H0.
    apply L10 in H0. auto.
    exists (fun x => M (length cand_all) (fst x) (snd x) <? s + 1).  
    simpl in *. split. apply Z.ltb_lt. omega.
    
    unfold coclosed. intros x; destruct x as (x, z); simpl in *.
    intros. apply Z.ltb_lt in H1. unfold W.
    apply andb_true_iff. split. unfold el. simpl. apply Z.ltb_lt.
    clear H. clear Heqs. clear X. clear H0.
    induction (length cand_all). simpl in *. omega.
    simpl in H1. apply Z.max_lub_lt_iff in H1. destruct H1. apply IHn. auto.

    unfold mp. apply forallb_forall. intros y Hy. unfold mpf.
    apply orb_true_iff. unfold el. simpl.
    assert (edge x y < s + 1 \/ edge x y >= s + 1) by omega.
    destruct H2. left. apply Z.ltb_lt. auto.
    right. apply Z.ltb_lt.
    assert (M (length cand_all) y z < s + 1 \/ M (length cand_all) y z >= s + 1) by omega.
    destruct H3. auto.
    apply L1 in H3.  pose proof (Evote.cons _ _ _ _ H2 H3).
    apply L2 in H4. destruct H4 as [n H4].
    pose proof (L4 x z n). omega.
  Defined.

  Lemma loses_prop_type : forall c, loses_prop c -> loses_type c.
  Proof.
    intros c H. unfold loses_prop, loses_type in *. apply L18.
    apply L16. auto.
  Qed.

  Lemma loses_type_prop : forall c, loses_type c -> loses_prop c.
  Proof.
    intros c H. unfold loses_prop, loses_type in *.
    destruct H as [k [d [Hp [f [Hf Hc]]]]].
    exists k, d. split. apply path_equivalence. auto.
    intros l H. pose proof (coclosed_path k f Hc).
    pose proof (H0 l _ _ H Hf). omega.
  Qed.
  
  Lemma wins_loses_M : forall c, (wins_type c) + (loses_type c).
  Proof.
    intros c. pose proof (L7 c). destruct H. left.
    unfold wins_type. apply L15. apply L14. intros d.
    pose proof (proj1 (forallb_forall _ cand_all) e d (cand_fin d)).
    simpl in H. apply Zle_bool_imp_le in H. apply Z.le_ge in H.
    remember (M (length cand_all) d c) as s. apply L1 in H.
    exists s. split. assumption.
    intros. rewrite Heqs. apply L2 in H0. destruct H0 as [n H0].
    apply Z.ge_le in H0. pose proof (L4 d c n). omega.

    right. apply L18. unfold c_wins in e. apply L11 in e.
    destruct e as [d [H1 H2]]. apply Z.leb_gt in H2. exists d. auto.
  Defined.

  Lemma first_one : 
    forall c : cand, c_wins c = true <-> (exists x : wins_type c, wins_loses_M c = inl x).
  Proof.
    split; intros. destruct (wins_loses_M c) eqn:Ht. exists w. auto. 
    pose proof (loses_type_prop c l). unfold loses_prop in H0.
    apply L16 in H0. pose proof (proj1 (L5 c) H). destruct H0. specialize (H1 x). omega.
    destruct H. pose proof (wins_type_prop c x). unfold wins_prop in H0.
    apply L5. apply L14. auto.
  Qed.

  Lemma second_one : 
    forall c : cand, c_wins c = false <-> (exists x : loses_type c, wins_loses_M c = inr x).
  Proof.
    split; intros. destruct (wins_loses_M c) eqn:Ht.
    pose proof (wins_type_prop c w).
    pose proof (proj1 (L6 c) H). unfold wins_prop in H0.
    pose proof (L14 c H0). destruct H1. specialize (H2 x). omega.
    exists l. auto.
    destruct H. pose proof (loses_type_prop c x). unfold loses_prop in H0.
    apply L6. apply L16. auto.
  Qed.
  

End Evote.

