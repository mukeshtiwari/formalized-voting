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
    |   [] => []
    |    c::cs => (c, c)::(all_pairs cs) ++ (map (fun x => (c, x)) cs) 
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
  Definition mpf (k: nat) (p : (cand * cand)%type) (l: list (cand * cand)%type) (b: cand) 
    := let a := fst p in let c := snd p in 
     (el k (a, b))  || (bool_in (b, c) l).
  Definition mp (k: nat) (p: (cand * cand)%type) (l: list (cand * cand)%type) := 
    let a := fst p in let c := snd p in
      forallb (mpf k p l) cand_all.

  (* W k is the dual of the operator the least fixpoint of which inductively defines paths *)
  (* W_k (l) = {(a, c) : edge a c <= k /\ forall b: (b, c) \in l \/edge a c <= k } *)
  (* Wf is the boolean predicate that expresses the operator *)
  Definition Wf k l :=  (fun p => andb (el k p)  (mp k p l) ).
  Definition W (k: nat) : list (cand * cand)%type -> list (cand *cand)%type :=
    fun l => filter (Wf k l) (all_pairs cand_all).

  (* a k-coclosed set is a set that is co-closed under W_k *)
  (* idea: the greatest co-closed (and indeed any co-closed set) only *)
  (* contains pairs (x, y) s.t. there's no path of strength >= k between x and y *)
  Definition coclosed (k: nat) (l: list (cand * cand)%type) :=
    forall x, In x l -> In x (W k l).

  (* evidence for winning a Schulze election. *)
  Definition ev (c: cand) := forall d : cand, existsT (k: nat),
    (PathT k c d) * (existsT (l: list (cand * cand)%type), In (d, c) l /\ coclosed k l).

  (* type-level paths allow to construct evidence for the existence of paths *)
  (* TODO: change name of lemma? *)
  Lemma equivalent : forall c d k , PathT k c d -> Path k c d.
  Proof.
    intros. induction X. apply unit. assumption.
    apply cons with (d := d). assumption.
    assumption.
  Qed.

  (* logical interpretation of the midpoint function *)
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

  (* generic property of coclosed sets as commented above *)
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
    apply coclosed_path with (x := d) (y := c) (l := l).
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
    fold_left (fun x => fun b => andb x (andb (elg k (a, b)) (f (b, c)))) cand_all true.

  Lemma mpg_true : forall k p f,
      mpg k p f = true <-> exists b, elg k (fst p, b) = true /\ f (b, snd p) = true. 
  Proof. Admitted.

  Definition Of k f := (fun p => orb (elg k p) (mpg k p f)).
  Definition O k : ((cand * cand) -> bool) -> ((cand * cand)-> bool) :=
    fun f => Of k f.


  Theorem wins_evi_1: forall k c d, Path k c d ->
                               exists (n : nat), Fixpoints.iter O (c, d) (fun _ => false) = true.
  
  
End Evote.
