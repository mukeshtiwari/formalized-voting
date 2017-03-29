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
Require Import schulzesynthesis.
Require Import Arith Wf.
Import ListNotations.
Open Scope Z.

Section Count.
  
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.
  
  Definition ballot := cand -> nat.

  (* ballot is valid if foreach candidate there is number greater than zero *)
  Definition ballot_valid (p : ballot) : Prop :=
    forall c : cand, (p c > 0)%nat.

  (* the following needs to be instantiated with a definition *)
  (* that ensures that m is the margin function of ballots bs *)
  Variable is_marg: (cand -> cand -> Z) -> (list ballot) -> Prop.
  
  (* the count proceeds in several stages, represented by the *)
  (* node type: checking ballots, computing margins and       *)
  (* determining winners + evidence.                         
  Inductive Node : Type :=
  | state : (list ballot * list ballot)  -> (cand -> cand -> Z) -> Node
  | done.
   *)

  Inductive Node : Type :=
  | state : (list ballot * list ballot)  -> (cand -> cand -> Z) -> Node
  | winners : (cand -> bool) ->  Node.

  
  (* earlier c d b means that c occurs earlier in the ballot b *)
  Definition earlier (c d : cand) (p : ballot) : Prop :=
    (p c > 0)%nat /\ (p d > 0)%nat /\ (p c < p d)%nat.

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
  
  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    intros b. pose proof in_decidable b cand_all.
    destruct H; [left | right]; firstorder. 
  Qed.

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

  
  (*
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
                 (forall c, (wins_type m c) + (loses_type m c)) -> Count bs done. 
   *)  
  


  
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
    pose proof (fin bs _ bs' (c_wins m) (wins_loses_M m cand_fin dec_cand cand_not_nil) X).
    pose proof (X0 (first_one m cand_fin dec_cand cand_not_nil)
                   (second_one m cand_fin dec_cand cand_not_nil)).
    exists (c_wins m). exists X1. apply I.
  Defined.
  (*
  Lemma final_count : forall (bs : list ballot), existsT (p : Count bs done), True.
  Proof.
    intros. pose proof (extract_prog bs). destruct X as [bs' [m X]].
    pose proof (fin _ _ _ X (wins_loses_M m cand_fin dec_cand cand_not_nil)). exists X0. apply I.
  Defined.
   *)
  
End Count.

