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
Import ListNotations.
Section Count.

  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
                                     : type_scope.
  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_fin : forall c : cand, In c cand_all.

  (* the following need to be substituted with viable notions *)
  (* of evidence for winning / losing with given margin.      *)

  Variable wins:  cand -> (cand -> cand -> Z) -> Type.
  Variable loses: cand -> (cand -> cand -> Z) -> Type.

  (* ballots are total preorders on cand, here represented by *)
  (* lists of lists where [[x1, x2], [x3], [x4, x5, x6]] is   *)
  (* interpreted as the ordering x1 = x2 > x3 > x4 = x5 = x6  *)
  (* i.e. x1 and x2 are equally ranked, both are preferred    *)
  (* over x3 and x3 is preferred over the equally ranked      *)
  (* candidates x4, x5 and x6.                                *)
  (*
  Definition ballot := list (list cand). *)

  (* new definition of ballot *)
  Definition ballot := cand -> nat.

  (* ballots are valid if every candidate is mentioned        *)
  (* precisely once.                                          *)
  (*
  Definition ballot_valid (b: ballot) : Prop :=
    (forall c: cand, In c (concat b)) /\ NoDup (concat b). *)

  Definition ballot_valid (p : ballot) : Prop :=
    forall c : cand, p c > 0.

 
 
  (* the following needs to be instantiated with a definition *)
  (* that ensures that m is the margin function of ballots bs *)
  Variable is_marg: (cand -> cand -> Z) -> (list ballot) -> Prop.

  (* the count proceeds in several stages, represented by the *)
  (* node type: checking ballots, computing margins and       *)
  (* determining winners + evidence.                          *)
  Inductive Node : Type :=
  | state : (list ballot * list ballot)  -> (cand -> cand -> Z) -> Node
  | done.

  (* state with uncounted and invalid votes so far *)



  (* earlier c d b means that c occurs earlier in the ballot b *)
  (*
  Definition earlier (c d: cand) (b: ballot) : Prop :=
    exists l1 lc l2 ld l3, b = l1++[lc]++l2++[ld]++l3 /\ In c lc /\ In d ld. *)

  Definition earlier (c d : cand) (p : ballot) : Prop :=
    p c > 0 /\ p d > 0 /\ (p c < p d).
  

  (*
  Definition equal (c d : cand) (b : ballot) : Prop :=
    exists l1 l l2, b = l1 ++ [l] ++ l2 /\ In c l /\ In d l. *)

  Definition equal (c d : cand) (p : ballot) : Prop :=
    p c > 0 /\ p d > 0 /\ p c = p d. 



  (* 
  Lemma equivalence : forall b : ballot, (forall c : cand, b c > 0) <->
                                    (forall c : cand, In c cand_all -> b c > 0).
  Proof.
    split; intros; firstorder.
  Qed. 

  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    pose proof NoDup_dec dec_cand.
    pose proof incl_dec dec_cand. intros b.
    unfold ballot_valid.
    destruct (X (concat b)).
    destruct (X0 cand_all (concat b)).
    left. firstorder.
    right. firstorder.
    destruct (X0 cand_all (concat b)).
    right. firstorder.
    right. firstorder.
  Qed. *)

  (* 
  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    intro.
    unfold ballot_valid.
    revert cand_fin.
    cut ({(forall c : cand, In c cand_all -> b c > 0)} +
         {~ (forall c : cand, In c cand_all -> b c > 0)}).
    intros.
      destruct H; firstorder.
      induction cand_all.
    firstorder.
      destruct IHl.
    destruct (le_gt_dec (b a) 0).
      right; intro.
        specialize (H a (or_introl eq_refl)).
        omega.
        left; intros.
      destruct H; auto; congruence.
      firstorder.
  Qed. *)

  Theorem in_decidable :
    forall (b : ballot) (l : list cand),
      {forall c : cand, In c l -> b c > 0} + {~(forall c : cand, In c l -> b c > 0)}.
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
    intros b. pose proof in_decidable b cand_all.
    destruct H; [left | right]; firstorder. 
  Qed.
  
  
  Definition nty (c d : cand) := 0%Z.

  Definition incdec (c d : cand) (t: cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
    (nt c d = t c d + 1)%Z /\
    (nt d c = t d c - 1)%Z.

  Definition nochange (c d : cand) (t : cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
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
   | fin m inbs : Count bs (state ([], inbs) m) ->
                  (forall c, (wins c m) + (loses c m)) -> Count bs done.

   
   Definition incdect (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
     fun c d =>
       match nat_compare_alt (p c) (p d) with
       | Lt => (m c d + 1)%Z
       | Eq => m c d
       | Gt => (m d c - 1)%Z
       end.

       
   Lemma incdec_proof : forall m (p : ballot) (c d : cand),
       (earlier c d p -> incdec c d m (incdect p m)) /\
       (equal c d p -> nochange c d m (incdect p m)).
   Proof.
     intros m p c d. split; intros.
     unfold earlier in H. unfold incdec. unfold incdect.
     destruct H as [H1 [H2 H3]]. split.
     destruct (p c), (p d); try omega.
   Admitted.
  
     
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
    intros bs. Check ax.
    pose proof (extract_prog_gen bs bs [] nty (ax bs bs nty eq_refl eq_refl)).
    destruct X as [i [m Hc]].
    exists i, m. assumption.
  Qed.
  
  Lemma wins_loses : forall c m, (wins c m) + (loses c m).
  Proof. Admitted.






   (* 
   
  (* the type Count describes how valid counts are conducted.  *)
  (* we interpret an element of Count n as evidence of a count *)
  (* having proceeded to stage n.                              *)
  Inductive Count (bs: list ballot): Node -> Type :=
  (*| chk : (forall b, In b bs -> ballot_valid b) -> Count bs checked *) (* added it for the moment *)
  | inv : forall b, In b bs -> ~ (ballot_valid b) -> Count bs (invalid b)
  | ax us t : us = bs -> t = nty -> (forall b, In b bs -> ballot_valid b) -> Count bs (state us t)
  | c1: forall u us m nm, Count bs (state (u :: us) m) ->
      (forall (c d: cand), (earlier c d u -> inc c d m nm) /\ (equal c d u -> nochange c d n nm)) ->
      Count bs (state us nm)           
  | fin: forall m, Count bs (state [] m) -> (forall c: cand, (wins c m) + (loses c m)) -> Count bs done.


  
  (* theorem to be proved: for all ballots, there exists a count *)
  (* that either ends in fin or inv. *)

 
  
  
 

  Theorem exists_count : forall (bs : list ballot), {b : ballot & Count bs (invalid b)}
                                               + Count bs (state bs nty).
  Proof.
    induction bs. right.
    apply chk. intros b H. inversion H.
    pose proof valid_or_invalid_ballot a as Ha.
    destruct Ha.
    destruct IHbs. left. destruct s. exists x.
    apply inv. inversion c. firstorder.
    unfold not; intros H. inversion c. firstorder.
    right. apply chk. intros. apply in_inv in H.
    destruct H. rewrite <- H. assumption.
    inversion c. specialize (H0 b0 H). assumption.
    left. exists a. apply inv. firstorder.
    assumption.
  Qed.

  Theorem exists_count_invalid_or_done :
    forall (bs : list ballot), {b : ballot & Count bs (invalid b)} + Count bs done.
  Proof.
    induction bs. right.
    eapply fin. constructor. auto.
    auto. intros b H. inversion H.
    

    pose proof valid_or_invalid_ballot a as Ha.
    destruct Ha. destruct IHbs. left. destruct s.
    exists x. apply inv. inversion c. firstorder.
    unfold not; intros H. inversion c. firstorder.
    right. 
    
    left. exists a. apply inv. firstorder.
    assumption. *)
  
  
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



  
  
  
  
