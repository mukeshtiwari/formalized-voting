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
Require Import ListLemma.
Import ListNotations.
Open Scope Z.

Section Schulze.

  (* candidates are a finite type with decidable equality *)
  Parameter cand : Type.
  Parameter cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.

  Section Evote.
    (** Section 2: Specification of Schulze Vote Counting **)

    (* marg is the margin in Schulze counting, i.e. marg c d is the number of 
       voters that perfer c over d. The existence of the margin function
       is assumed for the specification of Schulze Voting and will be
       constructed from incoming ballots later *)
    Variable marg : cand -> cand -> Z. 
    
    (* prop-level path *)
    Inductive Path (k: Z) : cand -> cand -> Prop :=
    | unit c d : marg c d >= k -> Path k c d
    | cons  c d e : marg c d >= k -> Path k d e -> Path k c e.
  
    (* winning condition of Schulze Voting *)
    Definition wins_prop (c: cand) :=
      forall d : cand, exists k : Z, 
          ((Path k c d) /\ (forall l, Path l d c -> l <= k)).
  
    (* dually, the notion of not winning: *)
    Definition loses_prop (c : cand) :=
      exists k d, Path k d c /\ (forall l, Path l c d -> l < k).
 
    (** Section 3 **)
  
    (* boolean function that determines whether the margin between a
       pair  of candidates is below a given integer *)
    Definition marg_lt (k : Z) (p : (cand * cand)) :=
      Zlt_bool (marg (fst p) (snd p)) k.
  
    (* definition of the (monotone) operator W_k that defines coclosed sets *)
    Definition W (k : Z) (p : cand * cand -> bool) (x : cand * cand) :=
      andb 
        (marg_lt k x) 
        (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all).

    (* k-coclosed predicates *)
    Definition coclosed (k : Z) (p : (cand * cand) -> bool) :=
      forall x, p x = true -> W k p x = true.

    (* type-level path to replace prop-level path *)
    Inductive PathT (k: Z) : cand -> cand -> Type :=
    | unitT : forall c d, marg c d >= k -> PathT k c d
    | consT : forall c d e, marg c d >= k -> PathT k d e -> PathT k c e.
  
    (* type-level winning condition in Schulze counting *)
    Definition wins_type c :=
      forall d : cand, existsT (k : Z),
      ((PathT k c d) *
       (existsT (f : (cand * cand) -> bool), f (d, c) = true /\ coclosed (k + 1) f))%type.

    (* dually, the type-level condition for non-winners *)
    Definition loses_type (c : cand) :=
      existsT (k : Z) (d : cand),
      ((PathT k d c) *
       (existsT (f : (cand * cand) -> bool), f (c, d) = true /\ coclosed k f))%type.

    (* type-level notions of winning and losing are equivalent *)
    (* auxilary lemmas needed for the proof of equivalence     *)
    (* search for wins_prop_type and wins_type_prop for the    *)
    (* statement and proof of equivalence, dually for losing.  *)
    
    (**** all lemmas needed for the proof of the below should go here ****)
  
    (* type-level paths allow to construct evidence for the existence of paths *)
    Lemma path_equivalence : forall c d k , PathT k c d -> Path k c d.
    Proof.
      intros c d k H.
      induction H; [constructor 1 | constructor 2 with d]; auto.
    Qed.

    Lemma mp_log : forall (k : Z) (x : cand * cand) (p : cand * cand -> bool),
        (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all) = true ->
        forall b, p (b, snd x) = true \/ marg (fst x) b < k.
    Proof.
      intros k x p H b.
      assert (Hin : In b cand_all) by  apply cand_fin.
      pose proof (proj1 (forallb_forall _ cand_all) H b Hin) as Hp. simpl in Hp.
      apply orb_true_iff in Hp; destruct Hp as [Hpl | Hpr]; destruct x as (a, c); simpl in *.
      + right; apply Zlt_is_lt_bool; auto.
      + left;auto.
    Qed.

    Lemma coclosed_path : forall k f, coclosed k f -> forall s x y,
          Path s x y -> f (x, y) = true -> s < k.
    Proof.
      intros k f Hcc x s y p. induction p.
      (* unit path *)
      + intros Hin; specialize (Hcc (c, d) Hin); apply andb_true_iff in Hcc;
          destruct Hcc as [Hccl Hccr]; apply Zlt_is_lt_bool in Hccl; simpl in Hccl;  omega.
      (* non unit path *)
      + intros Hin; specialize (Hcc (c, e) Hin); apply andb_true_iff in Hcc;
          destruct Hcc as [Hccl Hccr]; unfold marg_lt in Hccl; simpl in Hccl.
        assert (Hmp : forall m, f (m, (snd (c, e))) = true \/ marg (fst (c, e)) m < k)
          by (apply mp_log; auto); simpl in Hmp.
        specialize (Hmp d). destruct Hmp; [intuition | omega].
    Qed.

    (* the function M n maps a pair of candidates c, d to the strength of the strongest path of 
       length at most (n + 1) *)
    Fixpoint M (n : nat) (c d : cand) : Z :=
      match n with
      | 0%nat => marg c d 
      | S n' =>
        Z.max (M n' c d)
              (maxlist (map (fun x : cand => Z.min (marg c x) (M n' x d)) cand_all))
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
                                 (fun x : cand => Z.min (marg c x) (M n x d))).
      destruct H1.  clear H2. pose proof (H1 H0).
      destruct H2 as [e H2]. destruct H2.
      pose proof (Zminmax (marg c e) (M n e d) s). destruct H4.
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
      | [] => marg c d
      | (x :: xs) => Z.min (marg c x)  (str x xs d)
      end.
    
    Lemma path_len : forall k c d s l,
        (length l <= k)%nat -> str c l d >= s -> M k c d >= s.
    Proof.
      induction k. intros. assert ((length l <= 0)%nat -> l = []).
      { destruct l. intros. reflexivity.
        simpl in *. inversion H. }
      specialize (H1 H). subst. simpl in *. auto.
      intros. simpl in *. destruct l. simpl in *. apply Zmaxlemma.
      left. apply IHk with []. simpl. omega. simpl. auto.
      simpl in *. apply Zminmax in H0. destruct H0.
      apply Zmaxlemma. right. apply Max_of_nonempty_list.
      apply cand_not_nil. apply dec_cand. exists c0. split. specialize (cand_fin c0). trivial.
      apply Zminmax. split.
      omega. apply IHk with l. omega. omega.
    Qed.
    
    Lemma path_length : forall k c d s,
        M k c d >= s <-> exists (l : list cand), (length l <= k)%nat /\ str c l d >= s. 
    Proof.  
      split. generalize dependent s. generalize dependent d.
      generalize dependent c. induction k. simpl. intros. exists []. simpl. intuition.
      simpl. intros. pose proof (proj1 (Zmaxlemma (M k c d) _ s) H). destruct H0.
      specialize (IHk c d s H0). destruct IHk as [l [H1 H2]]. exists l. omega. clear H.
      pose proof
           (Max_of_nonempty_list _ cand_all cand_not_nil dec_cand s
                                 (fun x : cand => Z.min (marg c x) (M k x d))).
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
      assert ((marg c a) >= s /\ (str a l1 a0) >= s /\ str a0 l2 d >= s ->
              Z.min (marg c a) (str a l1 a0) >= s /\ str a0 l2 d >= s).
      { intros. destruct H1 as [H1 [H2 H3]]. split. apply Zminmax. auto. auto. }
      apply H1. split. assumption. apply IHl1. assumption.
      (* other part *)
      generalize dependent s. generalize dependent l2.
      generalize dependent a. generalize dependent d. generalize dependent c.
      induction l1; simpl; intros. apply Zminmax. auto.
      apply Zminmax. destruct H. apply Zminmax in H. destruct H.
      split. auto. apply IHl1. auto.
    Qed.
    
    Lemma str_lemma_1 : forall c d a l l1 l2 l3 s,
        l = l1 ++ a :: l2 ++ a :: l3 -> str c l d >= s -> str c (l1 ++ a :: l3) d >= s.
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
                        (ex_intro (fun l => (length l <= n)%nat /\ str c l d >= s) l (conj H3 H2))). omega.
      (* length l > length Evote.cand_all and there are candidates. Remove the duplicate
         candidate *)
      rewrite <- Hn in H3. assert (covers cand cand_all l).
      { unfold covers. intros. pose proof (cand_fin x). assumption. }
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
      { rewrite Heql0, H5.
        rewrite app_length. rewrite app_length.
        simpl. rewrite app_length. simpl.
        omega. }    
      rewrite H9 in H10. rewrite H8 in H10.
      assert (((k' + n) < (p + n))%nat -> (k' < p)%nat) by omega.
      specialize (H11 H10). assert (k' < k)%nat by omega.
      specialize (H k' H12 n c d Hn).
      pose proof (path_length (length l0) c d (str c l0 d)).
      destruct H13.
      assert ((exists l : list cand, (length l <= length l0)%nat /\ str c l d >= str c l0 d)).
      { exists l0. omega. }
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
      { intros. induction H. exists 0%nat. omega.
        assert ((v <= m)%nat -> (m >= v)%nat) by omega.
        specialize (H1 H). specialize (IHle H1). destruct IHle as [p H2].
        exists (S p). omega. }
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
           ?= maxlist (map (fun x : cand => Z.min (marg c x) (M n x d)) cand_all)).
      apply IHn. assumption.
      apply L9 in H. destruct H as [x [H1 H2]]. apply Zminmax in H2. destruct H2.
      specialize (IHn _ _ _ H0). specialize (consT _ _ _ _ H IHn). auto.
      apply cand_not_nil. apply dec_cand. apply IHn. assumption.
    Defined.
    
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
    
    Lemma L15 (c : cand) :
      (forall d, M (length cand_all) d c <= M (length cand_all) c d) -> wins_type c.
    Proof.
      unfold wins_type. intros. specialize (H d). remember (M (length cand_all) c d) as s.
      exists s. assert (H1 : M (length cand_all) c d >= s) by omega. clear Heqs.
      apply L10 in H1. split. auto.
      exists (fun x => M (length cand_all) (fst x) (snd x) <=? s). simpl in *. split.
      apply Z.leb_le. omega. unfold coclosed. intros. destruct x as (x, z).
      simpl in *. apply Z.leb_le in H0. unfold W. apply andb_true_iff. split.
      unfold marg_lt. simpl. apply Z.ltb_lt.
      induction (length cand_all). simpl in *. auto.
      simpl in H0. omega. simpl in H0. apply Z.max_lub_iff in H0.
      destruct H0. simpl in H. apply Z.max_lub_iff in H. destruct H.
      apply IHn; assumption.   
      apply forallb_forall.  intros y Hy. simpl in *.
      apply orb_true_iff. unfold marg_lt. simpl.
      assert (marg x y <= s \/ marg x y >= s + 1) by omega.
      destruct H2. left. apply Z.ltb_lt. omega.
      right. apply Z.leb_le.
      assert (M (length cand_all) y z <= s \/ M (length cand_all) y z >= s + 1) by omega.
      destruct H3. auto.
      apply L1 in H3. pose proof (cons _ _ _ _ H2 H3).
      apply L2 in H4. destruct H4 as [n H4].
      pose proof (L4 x z n). omega.
    Defined.
    
    (**** all generic lemmas about lists etc. should go elsewhere ****)
    
    (* the type level winning condition can be reconstruced from *)
    (* propositional knowledge of winning *)
    Lemma wins_prop_type : forall c, wins_prop c -> wins_type c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *.
      apply L15. apply L14. auto.
    Qed.
    
    (* dually, the type-level information witnessing winners *)
    (* entails prop-level knowledge. *)
    Lemma wins_type_prop : forall c, wins_type c -> wins_prop c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *. intros d.
      destruct (H d) as [k [H1 [f [H3 H4]]]].
      exists k. split. apply path_equivalence. auto.
      intros l H5. pose proof (coclosed_path _ _ H4).
      pose proof (H0 l _ _ H5 H3). omega.
    Qed.
    (* End of winning criteria *)
    
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
      (exists d, M (length cand_all) c d < M (length cand_all) d c) -> loses_type c.
    Proof.
      unfold loses_type. intros.
      pose proof
           (constructive_indefinite_ground_description
              _ f g L17 (constructive_prop c) (constructive_deci_cand c) H).
      destruct X as [d X]. unfold constructive_prop in X.
      remember (M (length cand_all) d c) as s. exists s, d.
      split. assert (H1 : M (length cand_all) d c >= s) by omega.
      apply L10 in H1. auto.
      exists (fun x => M (length cand_all) (fst x) (snd x) <? s).  
      simpl in *. split. apply Z.ltb_lt. omega.
      unfold coclosed. intros x; destruct x as (x, z); simpl in *.
      intros. apply Z.ltb_lt in H0. unfold W.
      apply andb_true_iff. split. unfold marg_lt. simpl. apply Z.ltb_lt.
      clear H. clear Heqs. clear X.
      induction (length cand_all). simpl in *. omega.
      simpl in H0. apply Z.max_lub_lt_iff in H0. destruct H0. apply IHn. auto.
      apply forallb_forall. intros y Hy.
      apply orb_true_iff. unfold marg_lt. simpl.
      assert (marg x y < s \/ marg x y >= s) by omega.
      destruct H1. left. apply Z.ltb_lt. auto.
      right. apply Z.ltb_lt.
      assert (M (length cand_all) y z < s \/ M (length cand_all) y z >= s) by omega.
      destruct H2. auto.
      apply L1 in H2.  pose proof (Evote.cons _ _ _ _ H1 H2).
      apply L2 in H3. destruct H3 as [n H3].
      pose proof (L4 x z n). omega.
    Defined.
    
    (* losing from type to prop level and prop to type level *)

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
    
    Lemma winner_one : 
      forall c : cand, c_wins c = true <-> (exists x : wins_type c, wins_loses_M c = inl x).
    Proof.
      split; intros. destruct (wins_loses_M c) eqn:Ht. exists w. auto. 
      pose proof (loses_type_prop c l). unfold loses_prop in H0.
      apply L16 in H0. pose proof (proj1 (L5 c) H). destruct H0. specialize (H1 x). omega.
      destruct H. pose proof (wins_type_prop c x). unfold wins_prop in H0.
      apply L5. apply L14. auto.
    Qed.
    
    Lemma loser_one : 
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
  
  Section Count.

    Definition ballot := cand -> nat.
    
    (* ballot is valid if foreach candidate there is number greater than zero *)
    Definition ballot_valid (p : ballot) : Prop :=
      forall c : cand, (p c > 0)%nat.
    
    Inductive Node : Type :=
    | state : (list ballot * list ballot)  -> (cand -> cand -> Z) -> Node
    | winners : (cand -> bool) ->  Node.
    
    (* earlier c d p means that c occurs earlier in the ballot p *)
    Definition earlier (c d : cand) (p : ballot) : Prop :=
      (p c > 0)%nat /\ (p d > 0)%nat /\ (p c < p d)%nat.
    
    (* equal c d p means that both c and d have same rank/preference in ballot p *)
    Definition equal (c d : cand) (p : ballot) : Prop :=
      (p c > 0)%nat /\ (p d > 0)%nat /\ (p c = p d)%nat.
    
    Theorem in_decidable :
      forall (b : ballot) (l : list cand),
        {forall c : cand, In c l -> (b c > 0)%nat} + {~(forall c : cand, In c l -> (b c > 0)%nat)}.
    Proof.
      intros b. induction l.
      left. intros. inversion H. 
      destruct IHl. destruct (le_gt_dec (b a) 0) as [H1 | H2].
      right. intro. pose proof (H a (or_introl eq_refl)). omega.
      left. firstorder. subst. assumption.
      right. firstorder.
    Qed.
    
    (* each ballot is either valid or invalid *)
    Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
    Proof.
      intros b. pose proof in_decidable b cand_all.
      destruct H; [left | right]; firstorder. 
    Qed.
    
    (* null tally *)
    Definition nty (c d : cand) := 0%Z.
    
    Definition incdec (c d : cand) (t: cand -> cand -> Z)
               (nt : cand -> cand -> Z) : Prop :=
      (nt c d = t c d + 1)%Z /\
      (nt d c = t d c - 1)%Z.
    
    Definition nochange (c d : cand) (t : cand -> cand -> Z)
               (nt : cand -> cand -> Z) : Prop :=
      nt c d = t c d.
    
    
    Inductive Count (bs : list ballot) : Node -> Type :=
    | ax us t : us = bs -> t = nty -> Count bs (state (us, []) t)
    | cvalid u us m nm inbs :
        Count bs (state (u :: us, inbs) m) -> ballot_valid u -> 
        (forall c d : cand, (earlier c d u -> incdec c d m nm) /\
                       (equal c d u -> nochange c d m nm)) ->
        Count bs (state (us, inbs) nm)
    | cinvalid u us m inbs :
        Count bs (state (u :: us, inbs) m) -> ~(ballot_valid u) ->
        Count bs (state (us, u :: inbs) m)
    | fin m inbs w (d : (forall c, (wins_type m c) + (loses_type m c))):
        Count bs (state ([], inbs) m) ->
        (forall c, w c = true <-> (exists x, d c = inl x)) ->
        (forall c, w c = false <-> (exists x, d c = inr x)) ->
        Count bs (winners w).
    
    Definition incdect (p : ballot) (m : cand -> cand -> Z) :
      cand -> cand -> Z :=
      fun c d =>
        match nat_compare_alt (p c) (p d) with
        | Lt => (m c d + 1)%Z
        | Eq => m c d
        | Gt => (m c d - 1)%Z
        end.
    
    
    Lemma incdec_proof : forall m (p : ballot) (c d : cand),
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
    Defined.
    
    Lemma extract_prog :
      forall (bs : list ballot), existsT i m, (Count bs (state ([], i) m)). 
    Proof.
      intros bs.
      pose proof (extract_prog_gen bs bs [] nty (ax bs bs nty eq_refl eq_refl)).
      destruct X as [i [m Hc]].
      exists i, m. assumption.
    Defined.
    
    Lemma final_count : forall (bs : list ballot), existsT (f : cand -> bool) (p : Count bs (winners f)), True.
    Proof.
      intros. pose proof (extract_prog bs). destruct X as [bs' [m X]].
      pose proof (fin bs m bs' (c_wins m) (wins_loses_M m) X (winner_one m) (loser_one m)).
      exists (c_wins m), X0. apply I.
    Defined.
    
  End Count.

End Schulze.

