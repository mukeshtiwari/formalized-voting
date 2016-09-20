Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import fp_finite_Dirk.
Import ListNotations.

Module Evote.  
  (* type level existential quantifier *)
  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

  
  (* candidates are a finite type with decidable equality *)
  Parameter cand : Type.
  Parameter cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.

  (* edge is the margin in Schulze counting, i.e. edge c d is the number of 
     voters that perfer c over d *)
  (* TODO: possibly rename? *)
  Parameter edge: cand -> cand -> nat.

  (* prop-level path *)
  Inductive Path (k: nat) : cand -> cand -> Prop :=
  | unit c d : edge c d >= k -> Path k c d
  | cons  c d e : edge c d >= k -> Path k d e -> Path k c e.

  (* type-level path *)
  Inductive PathT (k: nat) : cand -> cand -> Type :=
  | unitT : forall c d, edge c d >= k -> PathT k c d
  | consT : forall c d e, edge c d >= k -> PathT k d e -> PathT k c e.

  (* winning condition in Schulze counting *)
  Definition wins (c: cand) :=
    forall d : cand, exists k : nat, 
      ((Path k c d) /\ (forall l, Path l d c -> l <= k)).

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
    intro H. unfold cand_eqb in H. destruct (dec_cand c d). assumption. simpl in H. inversion H.
  Qed.

  (* boolean membership in lists of pairs *)
  Definition bool_in (p: (cand * cand)%type) (l: list (cand * cand)%type) :=
    existsb (fun q => (andb (cand_eqb (fst q) (fst p))) ((cand_eqb (snd q) (snd p)))) l. 

  (* towards the definition of co-closed sets *)
  (* el is a boolean function that returns true if the edge between two cands is <= k *)
  Definition el (k: nat) (p: (cand * cand)%type) := Compare_dec.leb (edge (fst p) (snd p)) k.

  (* mp k (a, c) l (for midpoint) returns true if there's a midpoint b st. either the edge between 
     a and c is <= k or else the pair (b, c) is in l *)
  (*
  Definition mpf (k: nat) (p : (cand * cand)%type) (l: list (cand * cand)%type) (b: cand) :=
    let a := fst p in
    let c := snd p in 
    (el k (a, b))  || (bool_in (b, c) l). *)
  
  Definition mpf (k : nat) (p : (cand * cand)%type) (f : (cand * cand) -> bool) (b : cand) :=
    let a := fst p in
    let c := snd p in
    (el k (a, b) || f (b, c)).
  (*
  Definition mp (k: nat) (p: (cand * cand)%type) (l: list (cand * cand)%type) := 
    let a := fst p in
    let c := snd p in
    forallb (mpf k p l) cand_all.
   *)

  Definition mp (k : nat) (p : (cand * cand)%type) (f : (cand * cand) -> bool) :=
    let a := fst p in
    let c := snd p in
    forallb (mpf k p f) cand_all.

  (* W k is the dual of the operator the least fixpoint of which inductively defines paths *)
  (* W_k (l) = {(a, c) : edge a c <= k /\ forall b: (b, c) \in l \/edge a c <= k } *)
  (* Wf is the boolean predicate that expresses the operator *)
  (* 
  Definition Wf k l :=  (fun p => andb (el k p)  (mp k p l) ).
  Definition W (k: nat) : list (cand * cand)%type -> list (cand *cand)%type :=
    fun l => filter (Wf k l) (all_pairs cand_all). *)

  Definition W (k : nat) := fun f => (fun p => andb (el k p) (mp k p f)).

  (* a k-coclosed set is a set that is co-closed under W_k *)
  (* idea: the greatest co-closed (and indeed any co-closed set) only *)
  (* contains pairs (x, y) s.t. there's no path of strength >= k between x and y *)
  (*
  Definition coclosed (k: nat) (l: list (cand * cand)%type) :=
    forall x, In x l -> In x (W k l). *)

  Definition coclosed (k : nat) (f : (cand * cand) -> bool) :=
    forall x, f x = true -> W k f x = true.

  (* evidence for winning a Schulze election. *)
  (*
  Definition ev (c: cand) := forall d : cand, existsT (k: nat),
    (PathT k c d) * (existsT (l: list (cand * cand)%type), In (d, c) l /\ coclosed k l).
   *)

  Definition ev (c : cand) := forall d : cand, existsT (k : nat),
    (PathT k c d) * (existsT (f : (cand * cand) -> bool), f (d, c) = true /\ coclosed k f).
                     
  (* type-level paths allow to construct evidence for the existence of paths *)
  (* TODO: change name of lemma? *)
  Lemma equivalent : forall c d k , PathT k c d -> Path k c d.
  Proof.
    intros. induction X. apply unit. assumption.
    apply cons with (d := d). assumption.
    assumption.
  Qed.

  (* logical interpretation of the midpoint function *)
  (*
  Lemma mp_log: forall k p l, mp k p l = true ->
    forall b, In (b, snd p) l \/ edge (fst p) b <= k.
  Proof.
    intros k p l H b.
    assert (Hin: In b cand_all).
    apply cand_fin.
    assert (Hp: In b cand_all  -> (mpf k p l) b = true).
    apply forallb_forall.
    unfold mp in H. assumption.
    specialize (Hp Hin).
    unfold mpf in Hp.
    assert (Hor: el k (fst p, b) = true \/ bool_in (b, snd p) l = true).
    apply orb_prop. assumption.
    destruct Hor as [Hl | Hr].
    (* case e k (fst p, b) = true *)
    unfold el in Hl. simpl in Hl.
    right.
    apply leb_complete. assumption.
    (* case bool_in ... *)
    left.
    unfold bool_in in Hr. simpl in Hr.
    assert (Hex: exists x, In x l /\ (fun q : cand * cand
                                => cand_eqb (fst q) b && cand_eqb (snd q) (snd p)) x = true).
    apply existsb_exists. assumption.     
    destruct Hex as [x Hx]. destruct Hx as [H1 H2].
    apply andb_true_iff in H2. destruct H2 as [H2 H3].
    apply cand_eqb_prop in H2.
    apply cand_eqb_prop in H3.
    destruct x. subst. simpl. simpl in H3. subst. assumption.
  Qed.
   *)

  Lemma mp_log : forall k p f,
      mp k p f = true -> forall b, f (b, snd p) = true \/ edge (fst p) b <= k.
  Proof.
    intros k p f H b.
    assert (Hin : In b cand_all). apply cand_fin.
    assert (Hp : In b cand_all -> (mpf k p f) b = true).
    apply forallb_forall. assumption.
    specialize (Hp Hin). apply orb_true_iff in Hp.
    destruct Hp as [Hpl | Hpr]. destruct p as (a, c).
    simpl in *. right. apply leb_complete. assumption.
    destruct p as (a, c). simpl in *. left. assumption.
  Qed.
  
      
  (* generic property of coclosed sets as commented above *)
  (*
  Lemma coclosed_path : forall k l, coclosed k l -> forall s x y,
    Path s x y -> In (x, y) l -> s <= k.
  Proof.
    intros k l Hcc.
    intros s x y.
    intro p.
    induction p.
    (* path of length one *)
    intro Hin.
    unfold coclosed in Hcc.
    specialize (Hcc (c, d)).
    specialize (Hcc Hin).
    unfold W in Hcc.
    Check filter_In.
    assert (HW: In (c, d) (all_pairs cand_all) /\  (Wf k l)  (c, d) = true).
    apply filter_In.
    assumption.
    destruct HW as [HW1 HW2].
    unfold Wf in HW2.

    assert ( el k (c, d) = true /\ mp k (c, d) l = true).
    apply andb_true_iff. assumption.
    destruct H0 as [He Hc].
    unfold el in He.
    simpl in He.
    assert (Hle: edge c d <= k). apply leb_complete. assumption.
    omega.
    (* non-unit path *)
    intro Hin.
    unfold coclosed in Hcc.
    specialize (Hcc (c, e)).   specialize (Hcc Hin). 
    unfold W in Hcc.
    assert (HW: In (c, e) (all_pairs cand_all) /\  (Wf k l)  (c, e) = true).
    apply filter_In. assumption.
    destruct HW as [HW1 HW2].
    unfold Wf in HW2.
    assert ( el k (c, e) = true /\ mp k (c, e) l = true).
    apply andb_true_iff. assumption.
    destruct H0 as [He Hc].
    unfold el in He.
    simpl in He.
    assert (Hle: edge c e <= k). apply leb_complete. assumption.
  (*  forall b, In (b, snd p) l \/ edge (fst p) b <= k. *)
    assert (Hmp: forall m, In (m, (snd (c, e))) l \/ edge (fst (c, e)) m <= k).
    apply  mp_log. assumption.
    simpl in Hmp.
    specialize (Hmp d).
    destruct Hmp as [Hm1 | Hm2].
    (* case 2nd part of path in coclosed list *)
    specialize (IHp Hm1).
    assumption.
    (* case first edge of small weight *)
    omega.
  Qed.
   *)
  
  Lemma coclosed_path : forall k f, coclosed k f -> forall s x y,
        Path s x y -> f (x, y) = true -> s <= k.
   Proof.
     intros k f Hcc x s y p. induction p.
     intros Hin. unfold coclosed in Hcc.
     specialize (Hcc (c, d) Hin). unfold W in Hcc.
     apply andb_true_iff in Hcc. destruct Hcc as [Hccl Hccr].
     apply leb_complete in Hccl. simpl in Hccl. omega.
     (* non unit path. *)
     intros Hin. unfold coclosed in Hcc. specialize (Hcc (c, e) Hin).
     unfold W in Hcc.  apply andb_true_iff in Hcc. destruct Hcc as [Hccl Hccr].
     unfold el in Hccl. simpl in Hccl. apply leb_complete in Hccl.
     assert (Hmp: forall m, f (m, (snd (c, e))) = true \/ edge (fst (c, e)) m <= k). apply mp_log.
     assumption. specialize (Hmp d). simpl in Hmp. destruct Hmp as [Hmp | Hmp].
     specialize (IHp Hmp). assumption. omega.
   Qed.

   
  Theorem th1: forall c, ev c -> wins c.
  Proof.
    intros c H.
    unfold wins. unfold ev in H.
    intro d.
    specialize (H d).
    destruct H as [k H].
    destruct H as [Hp Hc].
    exists k.
    split.
    apply equivalent. assumption.
    intros s p.
    destruct Hc as [l Hc].
    destruct Hc as [Hin Hcc].
    apply coclosed_path with (f := l) (x := d) (y := c).
    assumption.
    assumption.
    assumption.
  Qed.

  Definition geb (a b : nat) :=
    match ge_dec a b with
    | left _ => true
    | right _ => false
    end.

  Theorem geb_true : forall a b,
      geb a b = true <-> a >= b.
  Proof.
    split; intros. unfold geb in H. destruct ge_dec in H. assumption. inversion H.
    unfold geb. destruct ge_dec. reflexivity. congruence.
  Qed.
  
  (* elg is boolean function returns true if the edge between two candidates of >= k. *)
  Definition elg (k : nat) (p : (cand * cand)) : bool :=
    geb (edge (fst p) (snd p)) k.

  Lemma gebedge_true : forall c d k, edge c d >= k <->  geb (edge c d) k = true.
  Proof.
     split; intros. apply geb_true. assumption.
     apply geb_true. assumption.
  Qed.
  
  
  (* mp k (a, c) f (for midpoint) returns true if there's a midpoint b st.
     the edge between a and b is >= k /\ the function f (b, c) = true *)
  Definition mpg (k : nat) (p : (cand * cand)) (f : (cand * cand) -> bool) :=
    let a := fst p in
    let c := snd p in
    existsb (fun b  => andb (elg k (a, b)) (f (b, c))) cand_all.

  Definition O k := fun f => (fun p => orb (elg k p) (mpg k p f)).
  
  Theorem wins_evi_2 : forall k n c d,
      Fixpoints.iter (O k) n (fun _ : cand * cand => false) (c, d) = true ->
      Path k c d.
  Proof.
    intros k n.  induction n. intros c d H. inversion H.
    intros c d H. simpl in H. unfold O in H at 1.
    apply orb_true_iff in H. destruct H as [H | H].
    constructor 1. apply gebedge_true in H. simpl in H. assumption.
    unfold mpg in H. apply existsb_exists in H. destruct H as [m H].
    destruct H. apply andb_true_iff in H0. destruct H0 as [H1 H2].
    simpl in H1, H2.
    constructor 2 with (d := m). unfold elg in H1. simpl in H1.
    apply gebedge_true in H1. assumption.
    specialize (IHn m d). apply IHn. assumption.
  Qed.

  Theorem wins_evi: forall k c d,
      Path k c d <-> exists (n : nat), Fixpoints.iter (O k) n (fun _ => false) (c, d) = true.
  Proof.
    intros k c d. split. intros Hp. induction Hp.
    exists 1. simpl. unfold O. unfold elg. simpl.
    replace (geb (edge c d) k) with true. auto.
    symmetry. apply gebedge_true. congruence.
    destruct IHHp as [n IHHp].
    exists (S n). simpl. unfold O at 1.
    replace (mpg k (c, e) (Fixpoints.iter (O k) n (fun _ : cand * cand => false))) with true.
    apply orb_true_iff.  right. reflexivity.
    symmetry. unfold mpg. simpl.
    apply existsb_exists. exists d. split.
    apply cand_fin.
    apply andb_true_iff. split. unfold elg. simpl. apply gebedge_true. assumption.
    assumption.
    intros H. destruct H as [n H].
    apply (wins_evi_2 k n c d). assumption.
  Qed.


  Lemma monotone_operator : forall k, Fixpoints.mon (O k).
  Proof.
    intros k. unfold Fixpoints.mon. intros p1 p2 H.
    unfold O. unfold Fixpoints.pred_subset.
    unfold Fixpoints.pred_subset in H. intros a H1.
    apply orb_true_iff in H1. destruct H1 as [H1 | H1].
    apply orb_true_iff. left. assumption.
    apply orb_true_iff. right. unfold mpg.
    apply existsb_exists. simpl. unfold mpg in H1.
    apply existsb_exists in H1. destruct H1. exists x.
    split. destruct H0. assumption.
    apply andb_true_iff. split.
    destruct H0. apply andb_true_iff in H1. destruct H1. assumption.
    apply H. destruct H0. apply andb_true_iff in H1. destruct H1.
    assumption.
  Qed.
  
  Lemma all_pairsin: forall {A : Type} (a1 a2 : A) (l : list A),
      In a1 l -> In a2 l -> In (a1, a2) (all_pairs l).
  Proof.
    intros A a1 a2 l H1 H2. induction l.
    inversion H1. simpl.
    destruct H1 as [H3 | H3].
    {
      destruct H2 as [H4 | H4].
      left. congruence.
      right. apply in_app_iff. right.
      apply in_app_iff. left.
      rewrite H3. apply in_map. assumption.
    }
    {
      destruct H2 as [H4 | H4].
      right. apply in_app_iff.
      right. apply in_app_iff.
      right. rewrite H4. apply in_map_iff.
      exists a1. split. auto. auto.
      right. apply in_app_iff. left.
      apply IHl. assumption. assumption.
    }
  Qed.

  Lemma all_pairs_universal {A : Type} : forall (l : list A),
      (forall (a : A), In a l) -> forall (x : A * A), In x (all_pairs l).
  Proof.
    intros l H x. destruct x.
    apply all_pairsin. specialize (H a). assumption.
    specialize (H a0). assumption.
  Qed.
  
    
  Lemma length_pair : forall {A : Type} (n : nat) (l : list A),
      length l <= n -> length (all_pairs l) <= n * n.
  Proof.
    intros A n l. generalize dependent n. induction l.
    intros n H. auto with arith.
    intros n H. destruct n.
    inversion H.
    simpl. simpl in H.
    repeat rewrite app_length. repeat rewrite map_length.
    apply le_n_S. apply le_S_n in H.
    Open Scope nat_scope.
    replace (n * S n) with (n * n + n).
    repeat rewrite plus_assoc. replace (n + n * n + n) with (n * n + n + n).
    assert (Ht : length l <= n -> length (all_pairs l)  <= n * n -> 
                 length (all_pairs l) + length l + length l <= n * n + n + n) by omega.
    apply Ht. assumption. clear Ht.
    apply IHl. assumption.
    omega. rewrite mult_n_Sm. auto.
  Qed.

  Lemma length_cand : forall {A : Type} n , 
      Fixpoints.bounded_card A n -> Fixpoints.bounded_card (A * A) (n * n).
  Proof.
    intros A n. unfold Fixpoints.bounded_card.
    intros [l H]. exists (all_pairs l).
    destruct H as [H1 H2]. split. 
    intros (a1, a2). clear H2. induction l.
    pose proof (H1 a1). inversion H. simpl. 
    pose proof H1 a1. destruct H as [H3 | H3].
    {
      pose proof H1 a2.
      destruct H as [H4 | H4].
      left. congruence.
      right. apply in_app_iff. right.
      apply in_app_iff. left.
      rewrite H3. apply in_map. assumption.
    }
    {
      pose proof H1 a2.
      destruct H as [H4 | H4].
      right. apply in_app_iff.
      right. apply in_app_iff.
      right. rewrite H4. apply in_map_iff.
      exists a1. split. auto. auto.
      right. apply in_app_iff. left.
      apply all_pairsin. assumption.
      assumption.
    }

    apply length_pair. assumption.
  Qed.
  
  Theorem path_decidable :
    forall (k : nat) c d, {Path k c d} + {~(Path k c d)}.
  Proof.
    intros k c d.
    pose (cc := mult (length cand_all)  (length cand_all)%nat).
    destruct (bool_dec ((Fixpoints.iter (O k) cc (fun _  => false)) (c, d)) true) as [H | H].
    left. apply (wins_evi_2 k cc c d). assumption.
    apply not_true_is_false in H. right. intros Hp.
    apply wins_evi in Hp. destruct Hp as [n Hp].
    assert (Ht : Fixpoints.pred_subset (Fixpoints.iter (O k) n (fun _ => false))
                                       (Fixpoints.iter (O k) cc (fun _ => false))).
    apply Fixpoints.iter_fin. apply monotone_operator. 
    apply length_cand. unfold Fixpoints.bounded_card.
    exists cand_all. split. apply cand_fin. auto.
    unfold Fixpoints.pred_subset in Ht. specialize (Ht (c, d) Hp).
    congruence.
  Qed.

  Theorem path_lfp : forall (c d : cand) (k : nat),
      Fixpoints.least_fixed_point
        (cand * cand) (all_pairs cand_all)
        (all_pairs_universal cand_all cand_fin) (O k) (monotone_operator k) (c, d) = true 
      <-> Path k c d.
  Proof.
    split. intros H. apply wins_evi. exists (length (all_pairs cand_all)). assumption.
    intros H. apply wins_evi in H. destruct H as [n H]. unfold Fixpoints.least_fixed_point.
    unfold Fixpoints.empty_ss. remember (length (all_pairs cand_all)) as v.    
    specialize (Fixpoints.iter_fin v (O k) (monotone_operator k)). intros.
    unfold Fixpoints.bounded_card in H0.
    assert (Ht : (exists l : list (cand * cand), (forall a : cand * cand, In a l) /\ length l <= v)).
    {
      exists (all_pairs cand_all). split. apply (all_pairs_universal cand_all cand_fin).
      omega.
    }
    specialize (H0 Ht n). unfold Fixpoints.pred_subset in H0.
    apply H0. assumption.
  Qed.

  Check O.
  Check W.
  Theorem path_gfp : forall (c d : cand) (k : nat),
      Fixpoints.greatest_fixed_point
        (cand * cand) (all_pairs cand_all)
        (all_pairs_universal cand_all cand_fin) (W k) (monotone_operator k) (c, d) = true <->
      ~ (Path k c d).
  Proof.
    split. intros H Hp. unfold Fixpoints.greatest_fixed_point in H.
    unfold Fixpoints.full_ss in H. remember (length (all_pairs cand_all)) as v. 
    apply wins_evi in Hp. destruct Hp as [n Hp].
    

End Evote.
