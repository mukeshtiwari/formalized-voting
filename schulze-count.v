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
  Hypothesis cand_not_nil : Evote.cand_all <> nil.

  (* the following need to be substituted with viable notions *)
  (* of evidence for winning / losing with given margin.      *)

  Variable wins:  Evote.cand -> (Evote.cand -> Evote.cand -> Z) -> Type.
  Variable loses: Evote.cand -> (Evote.cand -> Evote.cand -> Z) -> Type.

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
    | S n' => maxlist (map (fun x : Evote.cand => Z.min (Evote.edge c x) (M n' x d)) Evote.cand_all)
    end.
  
  

  Lemma list_max : forall A:Type, forall l: list A, forall f: A -> nat,
          (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->(f b <= f m)%nat))).
  Proof.
    intros A l f.
    induction l as [| l0 ls IHls].
    (* l = [] *)
    left. trivial.
    (* l = l0::ls *)
    right. destruct IHls as [lsemp | lsnemp ].
    (* case ls = [] *)
    exists l0. split. apply (in_eq l0 ls).
    intros b H.
    assert (H0: l0 = b \/ In b ls) by apply (in_inv H).
    destruct H0 as [ eq | ctd].
    replace l0 with b. trivial.
    replace ls with ([]: list A) in ctd. contradict ctd.
    (* case ls <> [] *)
    destruct lsnemp as [maxls Hmax ]. destruct Hmax as [Hmaxin Hmaxgeq].
    assert (H: {(f maxls <= (f l0))%nat}  + {((f l0) <= (f maxls))%nat}) by apply (le_ge_dec (f maxls) (f l0)).
    destruct H as [Hl0 | Hmaxls].
    (* l0 is maxium *)
    exists l0. split. apply (in_eq l0 ls). intros b Hin.
    assert (H: l0 = b \/ In b ls) by apply (in_inv Hin).
    destruct H as [Heq | Hls ]. replace l0 with b. trivial.

    transitivity (f maxls). apply (Hmaxgeq b Hls). assumption.
    (* maxls is maximum *)
    exists maxls. split.
    apply (in_cons l0 maxls ls Hmaxin).
    intros b Hin.
    assert (H: l0 = b \/ In b ls) by apply (in_inv Hin). destruct H as [Heq | Htl].
    replace b with l0. assumption. apply (Hmaxgeq b Htl).
  Defined.

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

  
  (* induction on n *)  
  Lemma L1 : forall (n : nat) (s : Z) (c d : Evote.cand),
      M n c d >= s -> Evote.Path s c d.
  Proof.
    induction n. simpl. intros.
    constructor. auto.
    intros s c d H. simpl in H.
    pose proof
         (Max_of_nonempty_list _ Evote.cand_all cand_not_nil dec_cand s
                               (fun x : Evote.cand => Z.min (Evote.edge c x) (M n x d))).
    destruct H0. clear H1. pose proof (H0 H).
    destruct H1 as [e H1]. destruct H1.
    pose proof (Zminmax (Evote.edge c e) (M n e d) s). destruct H3.
    specialize (H3 H2). destruct H3.
    constructor 2 with (d := e). auto.
    apply IHn. assumption.
  Qed.

  
  (* induction on path *)
  Lemma L2 : forall (s : Z) (c d : Evote.cand),      
      Evote.Path s c d -> exists n, M n c d >= s.
  Proof.
    intros s c d H. induction H.
    exists O. auto. destruct IHPath.
    exists (S x). simpl. apply Max_of_nonempty_list.
    apply cand_not_nil. apply dec_cand. exists d.
    split. pose proof (cand_fin d). auto.
    apply Zminmax. split. auto. auto.
  Qed.

  
  Lemma L3 : forall (c d : Evote.cand) (n : nat),
      M n c d <= M (length Evote.cand_all) c d. 
  Proof. Admitted.

  Definition c_wins c :=
    forallb (fun d => (M (length Evote.cand_all) d c) <=? (M (length Evote.cand_all) c d))
            Evote.cand_all.


  
  (* 
  Lemma dec_cand_exists : existsT (cand_fun  : Evote.cand -> bool),
                          (forall c, Evote.wins c <-> cand_fun c = true).
  Proof. Admitted. *)
    
    
  Lemma wins_loses : forall c m, (wins c m) + (loses c m).
  Proof. Admitted.


  
End Count.


Inductive cand : Type :=
| a : cand
| b : cand
| c : cand.

Definition cand_all : list cand := [a; b; c].

Lemma finite_cand : forall c : cand, In c cand_all.
Proof.
  intros c0. destruct c0. unfold cand_all.
  firstorder. firstorder. firstorder.
Qed.

Lemma cand_decidable : forall c d : cand, {c = d} + {c <> d}.
Proof.
  decide equality.
Qed.

Definition one_vote := [[a]; [b]; [c]].
Check ballot_valid.

Lemma valid_vote : ballot_valid cand one_vote.
Proof.
  compute. firstorder. destruct c0; firstorder.
  constructor. unfold not. intros. destruct H. inversion H.
  inversion H. inversion H0. inversion H0.
  constructor. unfold not; intros. inversion H.
  inversion H0. inversion H0.
  constructor. unfold not; intros. inversion H.
  constructor.
Qed.
Check Count.

Definition wins (a : cand)  (m : cand -> cand -> Z) := nat.
Definition loses (a : cand) (m : cand -> cand -> Z) := nat.
Check Count.

Definition is_marg (m : cand -> cand -> Z) (bs : list (ballot cand)) := True.
Check Count.
Check checked.
Lemma l1 : Count cand wins loses [one_vote]
                 (checked cand).
Proof.
  constructor. intros. Check in_inv.
  apply in_inv in H. destruct H. rewrite <- H.
  apply valid_vote. inversion H.
Qed.

Check state.
Lemma l2 : Count cand wins loses [one_vote]
                 (state cand [one_vote] (fun (c d : cand) => 0%Z)).
Proof.
  constructor. auto. unfold nty. auto.
  intros b0 H. apply in_inv in H. destruct H.
  unfold ballot_valid. split.
  intros c0. rewrite <- H. unfold one_vote.
  simpl. destruct c0; intuition.
  rewrite <- H. simpl. constructor.
  unfold not; intros. apply in_inv in H0. destruct H0.
  inversion H0. apply in_inv in H0. destruct H0. inversion H0.
  inversion H0.
  constructor.
  unfold not; intros. apply in_inv in H0. destruct H0.
  inversion H0. inversion H0.
  constructor. unfold not; intros. inversion H0.
  constructor. inversion H.
Qed.

Definition margin_fun (c d : cand) : Z:=
  match c, d with
  |a, a => 0
  |a, b => 1
  |a, c => 1
  |b, a => -1
  |b, b => 0
  |b, c => 1
  |c, a => -1
  |c, b => -1
  |c, c => 0
  end.


Check Count.
Lemma l3 : Count cand wins loses [one_vote]
                 (state cand  [one_vote]  margin_fun).
Proof. Admitted.  



  
  
  
  
