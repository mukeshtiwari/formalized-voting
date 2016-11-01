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
  Definition ballot := list (list cand).

  (* ballots are valid if every candidate is mentioned        *)
  (* precisely once.                                          *)
  Definition ballot_valid (b: ballot) : Prop :=
    (forall c: cand, In c (concat b)) /\ NoDup (concat b).

  Print concat.
  Print flat_map.
  (* the following needs to be instantiated with a definition *)
  (* that ensures that m is the margin function of ballots bs *)
  Variable is_marg: (cand -> cand -> Z) -> (list ballot) -> Prop.

  (* the count proceeds in several stages, represented by the *)
  (* node type: checking ballots, computing margins and       *)
  (* determining winners + evidence.                          *)
  Inductive Node : Type :=
  | checked : Node
  | invalid : ballot -> Node
  | margin  : (cand -> cand -> Z) -> Node
  | counted (m: cand -> cand -> Z): (forall c, (wins c m) + (loses c m)) -> Node.

  Check counted.

  (* the type Count describes how valid counts are conducted.  *)
  (* we interpret an element of Count n as evidence of a count *)
  (* having proceeded to stage n.                              *)
  Inductive Count (bs: list ballot): Node -> Type :=
  | chk : (forall b, In b bs -> ballot_valid b) -> Count bs checked
  | inv : forall b, In b bs -> ~ (ballot_valid b) -> Count bs (invalid b)
  | mrg : Count bs checked -> forall m: cand -> cand -> Z,
      is_marg m bs -> Count bs (margin m)
  | fin : forall m, Count bs (margin m) -> forall r, Count bs (counted m r).


  (* theorem to be proved: for all ballots, there exists a count *)
  (* that either ends in fin or inv. *)

 

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
  
  Theorem exists_count : forall (bs : list ballot), {b : ballot & Count bs (invalid b)}
                                             + Count bs checked.
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

 
  Definition bool_in c l :=
    proj1_sig (bool_of_sumbool (in_dec dec_cand c l)).
  
  
  Fixpoint list_preorder l (c d : cand) : bool :=
    match l with
    | nil => false
    | h :: t =>
      match bool_in c h, bool_in d h with
      | true, true => false
      | true, false => true
      | false, true => false
      | false, false => list_preorder t c d
      end
      (*
      if andb (bool_in c h) (bool_in d h) then false
      else if andb (bool_in c h) (negb (bool_in d h)) then true
           else if andb (negb (bool_in c h)) (bool_in d h) then false
                else list_preorder t c d *)
    end.

  
                                  

  
   
    
    
