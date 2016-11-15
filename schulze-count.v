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

  Definition ballot_valid (b : ballot) : Prop :=
    (forall c : cand, exists (n : nat), b c = n).
  (* we don't need the NoDup logic for ballots as a function ? *)

  
  (* the following needs to be instantiated with a definition *)
  (* that ensures that m is the margin function of ballots bs *)
  Variable is_marg: (cand -> cand -> Z) -> (list ballot) -> Prop.

  (* the count proceeds in several stages, represented by the *)
  (* node type: checking ballots, computing margins and       *)
  (* determining winners + evidence.                          *)
  Inductive Node : Type :=
  | checked : Node (* we don't need this *)
  | invalid : ballot -> Node (* this either *)
  | state : (list ballot * list ballot)  -> (cand -> cand -> Z) -> Node
  | done.

  (* state with uncounted and invalid votes so far *)



  (* earlier c d b means that c occurs earlier in the ballot b *)
  (*
  Definition earlier (c d: cand) (b: ballot) : Prop :=
    exists l1 lc l2 ld l3, b = l1++[lc]++l2++[ld]++l3 /\ In c lc /\ In d ld. *)

  Definition earlier (c d : cand) (b : ballot) : Prop :=
    b c > 0 /\ b d > 0 /\ (b c > b d).

  (*
  Definition equal (c d : cand) (b : ballot) : Prop :=
    exists l1 l l2, b = l1 ++ [l] ++ l2 /\ In c l /\ In d l. *)

  Definition equal (c d : cand) (b : ballot) : Prop :=
    b c = b d. 

  (*
  (* Now we don't need the concept of ballot being valid or invalid ? *)

  Lemma equivalence : forall b : ballot, (forall c : cand, In c (concat b)) <->
                                    (forall c : cand, In c cand_all -> In c (concat b)).
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
  Qed.
   *)
  
  Definition nty (c d : cand) := 0%Z.

  Definition inc (c d : cand) (t: cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
    (nt c d = t c d + 1)%Z /\
    (nt d c = t d c - 1)%Z.

  Definition nochange (c d : cand) (t : cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
    nt c d = t c d.
  
  
   Inductive Count (bs : list ballot) : Node -> Type :=
   | ax us t : us = bs -> t = nty -> Count bs (state (us, []) t)
   | cvalid u us m nm inbs :
       Count bs (state (u :: us, inbs) m) -> ballot_valid u -> 
       (forall c d : cand, (earlier c d u -> inc c d m nm) /\
                      (equal c d u -> nochange c d m nm)) ->
       Count bs (state (us, inbs) nm)
   | cinvalid u us m inbs :
       Count bs (state (u :: us, inbs) m) -> ~(ballot_valid u) ->
       Count bs (state (us, u :: inbs) m)
   | fin m inbs : Count bs (state ([], inbs) m) ->
                  (forall c, (wins c m) + (loses c m)) -> Count bs done.
 

   
 
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
    assumption.
  
  
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



  
  
  
  
