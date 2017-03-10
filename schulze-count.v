(* prototype for evidence-producing Schulze counting *)

Require Import Coq.ZArith.ZArith. (* integers *)
Require Import Coq.Lists.List.    (* lists *)
Require Import Coq.Lists.ListDec.
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Schulze_Dirk_Z.
Require Import Arith Wf.
Import ListNotations.
Open Scope Z.
Section Count.

  
  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
  (*
  Variable cand : Type.
  Variable cand_all : list cand. *)
  (* Problem in importing the hypothesis from module Evote so leaving it for the moment *)
  Hypothesis dec_cand : forall n m : Evote.cand, {n = m} + {n <> m}.
  Hypothesis cand_fin : forall c : Evote.cand, In c Evote.cand_all.
  Hypothesis cand_not_nil :  (* exists c : Evote.cand, True. *) Evote.cand_all <> nil.

  (* the following need to be substituted with viable notions *)
  (* of evidence for winning / losing with given margin.      *)

  (* 
  Variable wins:  Evote.cand -> (Evote.cand -> Evote.cand -> Z) -> Type.
  Variable loses: Evote.cand -> (Evote.cand -> Evote.cand -> Z) -> Type.
   *)


  (* forall d, exists k, Path k c d /\ (forall l, Path l d c -> l <= k) *)
  Definition wins c (m : Evote.cand -> Evote.cand -> Z) :=
    forall d : Evote.cand, existsT (k : Z),
    ((Evote.PathT k c d) *
     (existsT (f : (Evote.cand * Evote.cand) -> bool),
      f (d, c) = true /\ Evote.coclosed (k + 1) f))%type.

  (* exists k d, Path k d c /\ (forall l, Path l c d -> l < k) *)
  Definition loses c (m : Evote.cand -> Evote.cand -> Z) :=
    existsT (k : Z) (d : Evote.cand),
    ((Evote.PathT k d c) *
     (existsT (f : (Evote.cand * Evote.cand) -> bool),
      f (c, d) = true /\ Evote.coclosed k f))%type.
  
  
  
  (* ballots are total preorders on cand, here represented by *)
  (* lists of lists where [[x1, x2], [x3], [x4, x5, x6]] is   *)
  (* interpreted as the ordering x1 = x2 > x3 > x4 = x5 = x6  *)
  (* i.e. x1 and x2 are equally ranked, both are preferred    *)
  (* over x3 and x3 is preferred over the equally ranked      *)
  (* candidates x4, x5 and x6.                                *)
  (*
  Definition ballot := list (list cand). *)

  (* new definition of ballot *)
  Definition ballot := Evote.cand -> nat.

  (* ballots are valid if every candidate is mentioned        *)
  (* precisely once.                                          *)
  (*
  Definition ballot_valid (b: ballot) : Prop :=
    (forall c: cand, In c (concat b)) /\ NoDup (concat b). *)

  Definition ballot_valid (p : ballot) : Prop :=
    forall c : Evote.cand, (p c > 0)%nat.

 
 
  (* the following needs to be instantiated with a definition *)
  (* that ensures that m is the margin function of ballots bs *)
  Variable is_marg: (Evote.cand -> Evote.cand -> Z) -> (list ballot) -> Prop.

  (* the count proceeds in several stages, represented by the *)
  (* node type: checking ballots, computing margins and       *)
  (* determining winners + evidence.                          *)
  Inductive Node : Type :=
  | state : (list ballot * list ballot)  -> (Evote.cand -> Evote.cand -> Z) -> Node
  | done.

  (* state with uncounted and invalid votes so far *)



  (* earlier c d b means that c occurs earlier in the ballot b *)
  (*
  Definition earlier (c d: cand) (b: ballot) : Prop :=
    exists l1 lc l2 ld l3, b = l1++[lc]++l2++[ld]++l3 /\ In c lc /\ In d ld. *)

  Definition earlier (c d : Evote.cand) (p : ballot) : Prop :=
    (p c > 0)%nat /\ (p d > 0)%nat /\ (p c < p d)%nat.
  

  (*
  Definition equal (c d : cand) (b : ballot) : Prop :=
    exists l1 l l2, b = l1 ++ [l] ++ l2 /\ In c l /\ In d l. *)

  Definition equal (c d : Evote.cand) (p : ballot) : Prop :=
    (p c > 0)%nat /\ (p d > 0)%nat /\ (p c = p d)%nat. 


  Theorem in_decidable :
    forall (b : ballot) (l : list Evote.cand),
      {forall c : Evote.cand, In c l -> (b c > 0)%nat} + {~(forall c : Evote.cand, In c l -> (b c > 0)%nat)}.
  Proof.
    intros b. induction l.
    left. intros. inversion H. 
    destruct IHl. destruct (le_gt_dec (b a) 0) as [H1 | H2].
    right. intro. pose proof (H a (or_introl eq_refl)). omega.
    left. firstorder. subst. assumption.
    right. firstorder.
  Qed.

  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    intros b. pose proof in_decidable b Evote.cand_all.
    destruct H; [left | right]; firstorder. 
  Qed.
  
  
  Definition nty (c d : Evote.cand) := 0%Z.

  Definition incdec (c d : Evote.cand) (t: Evote.cand -> Evote.cand -> Z)
             (nt : Evote.cand -> Evote.cand -> Z) : Prop :=
    (nt c d = t c d + 1)%Z /\
    (nt d c = t d c - 1)%Z.

  Definition nochange (c d : Evote.cand) (t : Evote.cand -> Evote.cand -> Z)
             (nt : Evote.cand -> Evote.cand -> Z) : Prop :=
    nt c d = t c d.
  
  
  Inductive Count (bs : list ballot) : Node -> Type :=
  | ax us t : us = bs -> t = nty -> Count bs (state (us, []) t)
  | cvalid u us m nm inbs :
      Count bs (state (u :: us, inbs) m) -> ballot_valid u -> 
      (forall c d : Evote.cand, (earlier c d u -> incdec c d m nm) /\
                     (equal c d u -> nochange c d m nm)) ->
      Count bs (state (us, inbs) nm)
  | cinvalid u us m inbs :
      Count bs (state (u :: us, inbs) m) -> ~(ballot_valid u) ->
      Count bs (state (us, u :: inbs) m)
  | fin m inbs : Count bs (state ([], inbs) m) ->
                 (forall c, (wins c m) + (loses c m)) -> Count bs done.

  
  Definition incdect (p : ballot) (m : Evote.cand -> Evote.cand -> Z) :
    Evote.cand -> Evote.cand -> Z :=
    fun c d =>
      match nat_compare_alt (p c) (p d) with
      | Lt => (m c d + 1)%Z
      | Eq => m c d
      | Gt => (m c d - 1)%Z
      end.

       
  Lemma incdec_proof : forall m (p : ballot) (c d : Evote.cand),
      (earlier c d p -> incdec c d m (incdect p m)) /\
      (equal c d p -> nochange c d m (incdect p m)).
  Proof.
    intros m p c d. split; intros.
    unfold earlier in H. unfold incdec. unfold incdect.
    destruct H as [H1 [H2 H3]]. split.
    unfold nat_compare_alt. destruct (lt_eq_lt_dec (p c) (p d)) eqn:H.
    destruct s. auto. omega. omega.
    unfold nat_compare_alt. destruct (lt_eq_lt_dec (p d) (p c)) eqn:H.
    destruct s. omega. omega. auto.
    unfold equal in H. destruct H as [H1 [H2 H3]].
    unfold nochange, incdect, nat_compare_alt.
    rewrite H3. destruct (lt_eq_lt_dec (p d) (p d)) eqn:H.
    destruct s; omega. omega.
  Qed.
   
  Lemma extract_prog_gen : forall bs u inbs m,
      Count bs (state (u, inbs) m) -> existsT i m, (Count bs (state ([], i) m)).
  Proof.
    intros bs. induction u.
    intros. exists inbs, m. auto.
    pose proof valid_or_invalid_ballot a.
    destruct H; swap 1 2. intros.
    pose proof (cinvalid bs a u m inbs X n).
    specialize (IHu (a :: inbs) m X0).
    destruct IHu as [Hinv [Hmar H3]].
    exists Hinv, Hmar. assumption.
    intros. pose proof (cvalid bs a u m (incdect a m) inbs X b (incdec_proof m a)).
    specialize (IHu inbs (incdect a m) X0). destruct IHu as [Hinv [Hm H]].
    exists Hinv, Hm. assumption.
  Qed.
    
  Lemma extract_prog :
     forall (bs : list ballot), existsT i m, (Count bs (state ([], i) m)). 
  Proof.
    intros bs.
    pose proof (extract_prog_gen bs bs [] nty (ax bs bs nty eq_refl eq_refl)).
    destruct X as [i [m Hc]].
    exists i, m. assumption.
  Qed.
  
  (* assume the definition for moment *)
  (* replace all the m with Evote.edge *)
  (*
  Definition c_wins (m : Evote.cand -> Evote.cand -> Z) : Evote.cand -> bool :=
    fun c => true.

  Lemma L0 : forall  (c : Evote.cand),
      c_wins Evote.edge c = true <-> Evote.wins c.
  Proof. Admitted.

  Check Evote.edge.

  
  Fixpoint M (n : nat) (c d : Evote.cand) (m : Evote.cand -> Evote.cand -> Z) : Z:=
    match n with
    | O => 0%Z
    | S n' => hd (0%Z) (map (fun x : Evote.cand => Z.min (m c x) (M n' x d m)) Evote.cand_all)
    end.
   *)

  Fixpoint maxlist (l : list Z) : Z :=
    match l with
    | [] => 0%Z
    | [h] => h
    | h :: t => Z.max h (maxlist t)
    end.

  Eval compute in (maxlist [-1; -2]).

  (* the function M n maps a pair of candidates c, d to the strength of the strongest path of 
     length at most (n + 1) *)
  Fixpoint M (n : nat) (c d : Evote.cand) : Z :=
    match n with
    | O => Evote.edge c d 
    | S n' =>
      Z.max (M n' c d)
            (maxlist (map (fun x : Evote.cand => Z.min (Evote.edge c x) (M n' x d)) Evote.cand_all))
    end.

  (*
  Theorem N : forall (n : nat) (c d : Evote.cand), n <> O -> Z.
    refine (fix MM (n : nat) (c d : Evote.cand) (H: n<>O) := _).
    destruct n as [|[|n'']].
    congruence.
    refine (Evote.edge c d).
    refine (maxlist
              (map (fun x : Evote.cand => Z.min (Evote.edge c x) (M (S n'') x d)) Evote.cand_all)).
  Defined.

   Program Fixpoint N (n : nat) (c d : Evote.cand) (H: n <> O) {struct n}: Z
    :=
      match n with
          | O => _
          | S n' =>
            match n' with
            | O => Evote.edge c d
            | S n'' =>
              maxlist (map (fun x : Evote.cand => Z.min (Evote.edge c x) (N n' x d _)) Evote.cand_all)
            end
      end.

   Print N. *)

  
  Lemma Zmn_lt : forall (m n : Z), m < n -> Z.max m n = n.
  Proof.
    intros m n H.
    unfold Z.max.
    rewrite (proj2 (Z.compare_lt_iff m n) H).
    auto.
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
  Lemma L1 : forall (n : nat) (s : Z) (c d : Evote.cand),
      M n c d >= s -> Evote.Path s c d.
  Proof.
    induction n. simpl. intros.
    constructor. auto.
    intros s c d H. simpl in H.
    pose proof (proj1 (Zmaxlemma (M n c d) _  s) H).
    destruct H0. pose proof (IHn _ _ _ H0). assumption.
    pose proof
         (Max_of_nonempty_list _ Evote.cand_all cand_not_nil dec_cand s
                               (fun x : Evote.cand => Z.min (Evote.edge c x) (M n x d))).
    destruct H1.  clear H2. pose proof (H1 H0).
    destruct H2 as [e H2]. destruct H2.
    pose proof (Zminmax (Evote.edge c e) (M n e d) s). destruct H4.
    specialize (H4 H3). destruct H4.
    constructor 2 with (d := e). auto.
    apply IHn. assumption.
  Qed.

  
  (* induction on path *)
  Lemma L2 : forall (s : Z) (c d : Evote.cand),      
      Evote.Path s c d -> exists n, M n c d >= s.
  Proof.
    intros s c d H. induction H.
    exists O. auto. destruct IHPath.
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
    | [] => Evote.edge c d
    | (x :: xs) => Z.min (Evote.edge c x)  (str x xs d)
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
      M k c d >= s <-> exists (l : list Evote.cand), (length l <= k)%nat /\ str c l d >= s. 
  Proof.  
    split. generalize dependent s. generalize dependent d.
    generalize dependent c.
    induction k. simpl. intros. exists []. simpl. intuition.

    simpl. intros.
    pose proof (proj1 (Zmaxlemma (M k c d) _ s) H). destruct H0.
    specialize (IHk c d s H0). destruct IHk as [l [H1 H2]]. exists l. omega.
    clear H.
    pose proof
         (Max_of_nonempty_list _ Evote.cand_all cand_not_nil dec_cand s
                               (fun x : Evote.cand => Z.min (Evote.edge c x) (M k x d))).
    
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
    assert ((Evote.edge c a) >= s /\ (str a l1 a0) >= s /\ str a0 l2 d >= s ->
            Z.min (Evote.edge c a) (str a l1 a0) >= s /\ str a0 l2 d >= s).
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


  Lemma list_and_num : forall (A : Type) (n : nat) (l : list A),
      (length l > n)%nat -> exists p, (length l = p + n)%nat.
  Proof.
    intros A n l H. induction l. inversion H.
    simpl in *. apply gt_S in H. destruct H. specialize (IHl H). destruct IHl as [p IHl].
    exists (S p). omega. exists 1%nat. omega.
  Qed.

  
  Lemma L3 : forall k n c d (Hn: (length Evote.cand_all = n)%nat),
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
    rewrite <- Hn in H3. assert (covers Evote.cand Evote.cand_all l).
    {
      unfold covers. intros. pose proof (cand_fin x). assumption.
    }
    pose proof (list_finite_elem _ n Evote.cand_all dec_cand Hn l H3 H4).
    destruct H5 as [a [l1 [l2 [l3 H5]]]].
    pose proof (str_lemma_1 _ _ _ _ _ _ _ _ H5 H2).
    remember (l1 ++ a :: l3) as l0.
    assert ((length l0 <= n)%nat \/ (length l0 > n)%nat) by omega.
    destruct H7.
    pose proof (path_length n c d s). destruct H8.
    assert ((exists l : list Evote.cand, (length l <= n)%nat /\ str c l d >= s)).
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
    assert ((exists l : list Evote.cand, (length l <= length l0)%nat /\ str c l d >= str c l0 d)).
    {
      exists l0. omega.
    }
    specialize (H14 H15). clear H13. rewrite <- H9 in H. omega.
  Qed.
  
  
      
    
  Lemma L4 : forall (c d : Evote.cand) (n : nat),
      M n c d <= M (length Evote.cand_all) c d. 
  Proof.
    intros c d n. assert ((n <= (length Evote.cand_all))%nat \/
                          (n >= (length Evote.cand_all))%nat) by omega.
    destruct H. apply monotone_M. assumption.
    remember ((length Evote.cand_all)) as v.
    assert ((n >= v)%nat -> exists p, (n = p + v)%nat).
    {
      intros. induction H. exists O%nat. omega.
      assert ((v <= m)%nat -> (m >= v)%nat) by omega.
      specialize (H1 H). specialize (IHle H1). destruct IHle as [p H2].
      exists (S p). omega.
    }
      
    specialize (H0 H). destruct H0 as [p H0].
    subst. apply L3. auto.
  Qed.
  
  
  Definition c_wins c :=
    forallb (fun d => (M (length Evote.cand_all) d c) <=? (M (length Evote.cand_all) c d))
            Evote.cand_all.

  Lemma L5 (c : Evote.cand) :
    c_wins c = true <-> forall d, M (length Evote.cand_all) d c <= M (length Evote.cand_all) c d. 
  Proof.
    split; intros.
    unfold c_wins in H.
    pose proof
         (proj1 (forallb_forall
                   (fun d : Evote.cand => M (length Evote.cand_all) d c <=?
                                       M (length Evote.cand_all) c d) Evote.cand_all) H).
    pose proof (H0 d (cand_fin d)). simpl in H1.
    apply Zle_bool_imp_le. assumption.

    unfold c_wins. apply forallb_forall. intros x Hin.
    pose proof H x. apply Zle_imp_le_bool. assumption.
  Qed.

  Lemma L6 (c : Evote.cand) :
    c_wins c = false <-> exists d, M (length Evote.cand_all) c d < M (length Evote.cand_all) d c.
  Proof.
    split; intros. unfold c_wins in H.
    apply Evote.forallb_false in H. destruct H as [x [H1 H2]].
    exists x. apply Z.leb_gt in H2. omega.

    destruct H as [d H]. unfold c_wins. apply Evote.forallb_false.
    exists d. split. pose proof (cand_fin d). assumption.
    apply Z.leb_gt. omega.
  Qed.


  Lemma L7 : forall c, {c_wins c = true} + {c_wins c = false}.
  Proof.
    intros c. destruct (c_wins c) eqn:Ht. left. reflexivity.
    right. reflexivity.
  Qed.


  (* this proof is exact copy of L2 *)
  Lemma L8 : forall (s : Z) (c d : Evote.cand),
      Evote.PathT s c d -> exists n, M n c d >= s.
  Proof.
    intros s c d H. 
    induction H. exists 0%nat. auto.
    destruct IHPathT. exists (S x). simpl.
    apply Zmaxlemma. right.
    apply Max_of_nonempty_list. apply cand_not_nil.
    apply dec_cand. exists d. split. pose proof (cand_fin d). auto.
    apply Zminmax. auto.
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
  Qed.
  
    
  Lemma L10 : forall n s c d, M n c d >= s -> Evote.PathT s c d.
  Proof.
    induction n; simpl; intros. constructor. auto.
    unfold Z.max in H.
    destruct 
      (M n c d
         ?= maxlist (map (fun x : Evote.cand => Z.min (Evote.edge c x) (M n x d)) Evote.cand_all)).
    apply IHn. assumption.
    apply L9 in H. destruct H as [x [H1 H2]]. apply Zminmax in H2. destruct H2.
    specialize (IHn _ _ _ H0). specialize (Evote.consT _ _ _ _ H IHn). auto.
    apply cand_not_nil. apply dec_cand. apply IHn. assumption.
  Qed.
  
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

  Lemma L12 : forall c d k,
      Evote.Path k d c /\ (forall l, Evote.Path l c d -> l < k) ->
      existsT (k : Z) (d : Evote.cand), ((Evote.PathT k d c) *
     (existsT (f : (Evote.cand * Evote.cand) -> bool),
      f (c, d) = true /\ Evote.coclosed k f))%type.
  Proof.
    intros c d k H. destruct H. exists k, d.
    split. apply L10 with (length Evote.cand_all).
    apply L2 in H. destruct H as [n H].
    pose proof (L4 d c n). omega.
    unfold Evote.coclosed.
    Require Import fp_finite_Dirk.
    exists (Fixpoints.greatest_fixed_point _ _ (Evote.all_pairs_universal Evote.cand_all cand_fin)
                                      (Evote.W k) (Evote.monotone_operator_w k)).
    split. apply Evote.path_gfp. unfold not. intros.
    pose proof (H0 k H1). omega.

    intros. destruct x.
    apply Fixpoints.fixed_point_is_coclosed.  apply Fixpoints.greatest_fixed_point_is_fixed_point.
    auto.
  Qed.
  
    
  Lemma wins_loses : forall c, (wins c Evote.edge) + (loses c Evote.edge).
  Proof. 
    intros c. pose proof (L7 c). destruct H. left.
    apply Evote.th2. unfold Evote.wins, c_wins in *. intros d.
    pose proof (proj1 (forallb_forall _ Evote.cand_all) e d (cand_fin d)).
    simpl in H. apply Zle_bool_imp_le in H. apply Z.le_ge in H.
    remember (M (length Evote.cand_all) d c) as s. apply L1 in H. 
    exists s. split. assumption.
    intros. rewrite Heqs. apply L2 in H0. destruct H0 as [n H0].
    apply Z.ge_le in H0. pose proof (L4 d c n). omega.

    
    right. unfold loses, c_wins in *. apply L11 in e. destruct e as [d [H1 H2]].
    apply Z.leb_gt in H2. apply L12 with (d := d) (k := M (length Evote.cand_all) d c).
    split. remember (M (length Evote.cand_all) d c) as s. apply L1 with (length Evote.cand_all).
    omega.

    intros l H. apply L2 in H. destruct H as [n H].
    pose proof (L4 c d n). omega.
  Qed.
  
  (* project finished *)
  (* Try to connect Prop level with Matrix *)
  
  Lemma L13 (c : Evote.cand) : forall d k,
        Evote.Path k c d /\ (forall l, Evote.Path l d c -> l <= k) ->
        M (length Evote.cand_all) d c <= M (length Evote.cand_all) c d.
  Proof.
    intros d k [H1 H2].
    remember (M (length Evote.cand_all) d c) as s.
    apply Z.eq_le_incl in Heqs.
    apply Z.le_ge in Heqs.
    pose proof (L1 _ _ _ _ Heqs). specialize (H2 s H).
    apply L2 in H1. destruct H1 as [n H1].
    pose proof (L4 c d n). omega.
  Qed.

  Lemma L14 (c : Evote.cand) :
    (forall d, exists k, Evote.Path k c d /\ (forall l, Evote.Path l d c -> l <= k)) ->
    forall d, M (length Evote.cand_all) d c <= M (length Evote.cand_all) c d.
  Proof.
    intros. specialize (H d). destruct H as [k [H1 H2]]. apply L13 with k.
    intuition.
  Qed.
  
  Lemma L15 (c : Evote.cand) : (forall d,
      M (length Evote.cand_all) d c <= M (length Evote.cand_all) c d) ->
      forall d : Evote.cand, existsT (k : Z),
    ((Evote.PathT k c d) *
     (existsT (f : (Evote.cand * Evote.cand) -> bool),
      f (d, c) = true /\ Evote.coclosed (k + 1) f))%type.
  Proof.
    intros. specialize (H d). remember (M (length Evote.cand_all) d c) as s.
    exists s. apply Z.le_ge in H. apply L10 in H. split. auto.
    exists (fun x => M (length Evote.cand_all) (fst x) (snd x) <=? s). simpl in *. split.
    apply Z.leb_le. omega.
  
    unfold Evote.coclosed. intros. destruct x as (x, z). simpl in *.
    apply Z.leb_le in H0. unfold Evote.W. apply andb_true_iff. split.
    unfold Evote.el. simpl. apply Z.ltb_lt.
    assert (Evote.edge x z <= s -> Evote.edge x z < s + 1) by omega.
    apply H1. clear H1. clear Heqs.
    induction (length Evote.cand_all). simpl in *. auto.
    simpl in H0. apply Z.max_lub_iff in H0.
    destruct H0. specialize (IHn H0). auto.
    
    unfold Evote.mp. apply forallb_forall. intros y Hy.  unfold Evote.mpf. simpl in *.
    apply orb_true_iff. unfold Evote.el. simpl.
    assert (Evote.edge x y <= s \/ Evote.edge x y >= s + 1) by omega.
    destruct H1. left. apply Z.ltb_lt. omega.
    right. apply Z.leb_le.
    assert (M (length Evote.cand_all) y z <= s \/ M (length Evote.cand_all) y z >= s + 1) by omega.
    destruct H2. auto.
    apply L1 in H2. pose proof (Evote.cons _ _ _ _ H1 H2).
    apply L2 in H3. destruct H3 as [n H3].
    pose proof (L4 x z n). omega.
  Qed.


  (* losing using M function *)
  Lemma L16 (c : Evote.cand) :
    (exists k d, Evote.Path k d c /\ (forall l, Evote.Path l c d -> l < k)) ->
    (exists d, M (length Evote.cand_all) c d < M (length Evote.cand_all) d c).
  Proof.
    intros. destruct H as [k [d [H1 H2]]].
    exists d. remember (M (length Evote.cand_all) c d)  as s.
    pose proof (Z.eq_le_incl _ _ Heqs) as H3.
    apply Z.le_ge in H3. apply L1 in H3. specialize (H2 s H3).
    apply L2 in H1. destruct H1 as [n H1].
    pose proof (L4 d c n). omega.
  Qed.

  Require Import Coq.Logic.ConstructiveEpsilon.
  
  Definition constructive_prop (c d : Evote.cand):=
     M (length Evote.cand_all) c d < M (length Evote.cand_all) d c.

  Lemma constructive_deci_cand : forall (c d : Evote.cand),
      {(constructive_prop c d)} + {~(constructive_prop c d)}.
  Proof.
    intros c d. unfold constructive_prop.
    pose proof (Z_lt_ge_bool (M (length Evote.cand_all) c d) (M (length Evote.cand_all) d c)).
    destruct H. destruct x. left. auto.
    right. apply Zle_not_lt. omega.
  Qed.

  Require Import Coq.Program.Wf.
  Program Fixpoint find_cand (c : Evote.cand) (l : list Evote.cand) (H : In c l) : nat :=
    match l with
    | [] => _
    | h :: t => if dec_cand c h then O
               else S (find_cand c t _)
    end.
  Next Obligation.
    inversion H.
  Defined.
  Next Obligation.
    simpl in H. destruct H. symmetry in H.
    pose proof (H0 H). inversion H1. assumption.
  Defined.
  
  Definition f_cand_nat (c : Evote.cand) := find_cand c Evote.cand_all (cand_fin c).

  Program Fixpoint find_nat (n : nat) (l : list Evote.cand) (H : l <> nil) : Evote.cand :=
    match l with
    | [] => _
    | h :: t =>
      match n with
      | O => h
      | S n' =>
        match t with
        | [] => h
        | _ => find_nat n' t _
        end
      end
    end. 
  
  Definition g_nat_cand (n : nat) := find_nat n (Evote.cand_all) (cand_not_nil). 

  Lemma L17 : forall c, g_nat_cand (f_cand_nat c) = c.
  Proof.
    intros c. unfold g_nat_cand, f_cand_nat.
    Admitted.
    
    
  Lemma L18 (c : Evote.cand) :
    (exists d, M (length Evote.cand_all) c d < M (length Evote.cand_all) d c) ->
    (existsT (k : Z) (d : Evote.cand),
     ((Evote.PathT k d c) *
      (existsT (f : (Evote.cand * Evote.cand) -> bool),
       f (c, d) = true /\ Evote.coclosed k f))%type).
  Proof.
    intros.
    pose proof
         (constructive_indefinite_ground_description
            _ f_cand_nat g_nat_cand L17 (constructive_prop c) (constructive_deci_cand c) H).
    destruct X as [d X]. unfold constructive_prop in X.
    remember (M (length Evote.cand_all) c d) as s. exists s, d.
    split. apply Z.lt_le_incl in X. apply Z.le_ge in X.
    apply L10 in X. auto.
    exists (fun x => M (length Evote.cand_all) (fst x) (snd x) <? s).  
    simpl in *. split. apply Z.ltb_lt. admit.
    
    unfold Evote.coclosed. intros x; destruct x as (x, z); simpl in *.
    intros. apply Z.ltb_lt in H0. unfold Evote.W.
    apply andb_true_iff. split. unfold Evote.el. simpl. apply Z.ltb_lt.
    clear H. clear Heqs. clear X.
    induction (length Evote.cand_all). simpl in *. omega.
    simpl in H0. apply Z.max_lub_lt_iff in H0. destruct H0. apply IHn. auto.

    unfold Evote.mp. apply forallb_forall. intros y Hy. unfold Evote.mpf.
    apply orb_true_iff. unfold Evote.el. simpl.
    assert (Evote.edge x y < s \/ Evote.edge x y >= s) by omega.
    destruct H1. left. apply Z.ltb_lt. auto.
    right. apply Z.ltb_lt.
    assert (M (length Evote.cand_all) y z < s \/ M (length Evote.cand_all) y z >= s) by omega.
    destruct H2. auto.
    apply L1 in H2.  pose proof (Evote.cons _ _ _ _ H1 H2).
    apply L2 in H3. destruct H3 as [n H3].
    pose proof (L4 x z n). omega.
    
End Count.
