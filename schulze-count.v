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
  | counted (m: cand -> cand -> Z): (forall c, (wins c m) + (loses c m)) -> Node
  | state : (list ballot * list ballot) -> (cand -> cand -> Z) -> Node.

  Check counted.

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

  Definition nty (c d : cand) := 0%Z.

  Definition inc (c d : cand) (t: cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
    (nt c d = t c d + 1)%Z /\
    (nt d c = t d c - 1)%Z.

  Definition dec (c d : cand) (t : cand -> cand -> Z) (nt : cand -> cand -> Z) : Prop :=
    nt c d = t c d.

  (* the type Count describes how valid counts are conducted.  *)
  (* we interpret an element of Count n as evidence of a count *)
  (* having proceeded to stage n.                              *)
  Inductive Count (bs: list ballot): Node -> Type :=
  | chk : (forall b, In b bs -> ballot_valid b) -> Count bs checked
  | inv : forall b, In b bs -> ~ (ballot_valid b) -> Count bs (invalid b)
  | mrg : Count bs checked -> forall m: cand -> cand -> Z,
        is_marg m bs -> Count bs (margin m)
  | fin : forall m, Count bs (margin m) -> forall r, Count bs (counted m r)
  | ax us t : us = bs -> t = nty -> Count bs (state ([], us) t) (* mine addition *)
  | c1 u0 m u1 t nt :
      bs = (u0 ++ [m] ++ u1) -> Count bs (state (u0, m :: u1) t) ->
      (forall (c : cand), (forall (d : cand), list_preorder m c d = true -> inc c d t nt)) ->
      Count bs (state (u0 ++ [m] , u1) nt)          
  | c2  u0 m u1 t nt :
      bs = (u0 ++ [m] ++ u1) -> Count bs (state (u0, m :: u1) t) ->
      (forall (c : cand), (forall (d : cand), list_preorder m c d = false -> dec c d t nt)) ->
      Count bs (state (u0 ++ [m] , u1) nt) 
  | c3 m r t us : us = bs ->  Count bs (state (us, []) t) -> m = t -> Count bs (counted m r).
  (* replacing m with t is not working *)
  
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
Lemma l1 : Count cand cand_decidable wins loses is_marg [one_vote]
                 (checked cand wins loses).
Proof.
  constructor. intros. Check in_inv.
  apply in_inv in H. destruct H. rewrite <- H.
  apply valid_vote. inversion H.
Qed.
Check state.
Lemma l2 : Count cand cand_decidable wins loses is_marg [one_vote]
                 (state cand wins loses ([], [one_vote]) (fun (c d : cand) => 0%Z)).
Proof.
  constructor. auto. unfold nty. auto.
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

Lemma l3 : Count cand cand_decidable wins loses is_marg [one_vote]
                 (state cand wins loses ([one_vote], []) margin_fun).
Proof.
  Check c1.
  apply (c1 cand cand_decidable wins loses is_marg [one_vote] [] one_vote [] (nty cand) margin_fun). auto.
  apply l2. intros c d H.
  unfold inc. split.
  unfold margin_fun. destruct c.
  destruct d. unfold one_vote in H.
  simpl in H.
  replace ( bool_in cand cand_decidable a [a]) with true in H.
  inversion H. unfold bool_in.
  simpl (in_dec cand_decidable a [a]).
  destruct (cand_decidable a a) eqn : H1. simpl.
  auto. unfold not in n.
  pose proof (n eq_refl). inversion H0.
  simpl. auto. simpl. auto.
  destruct d. unfold one_vote in H.
  unfold list_preorder in H.
  replace (bool_in cand cand_decidable b [a]) with false in H.
  replace (bool_in cand cand_decidable a [a]) with true in H.
  inversion H. unfold bool_in.
  simpl (in_dec cand_decidable a [a]).
  destruct (cand_decidable a a). auto.
  unfold not in n. pose proof (n eq_refl). inversion H0.
  unfold bool_in.
  simpl (in_dec cand_decidable b [a]).
  destruct (cand_decidable a b). inversion e.
  simpl. auto.
  unfold one_vote in H.
  unfold list_preorder in H.
  replace (bool_in cand cand_decidable b [a]) with false in H.
  replace (bool_in cand cand_decidable b [b]) with true in H.
  inversion H. unfold bool_in.
  simpl (in_dec cand_decidable b [b]).
  destruct (cand_decidable b b). auto.
  pose proof (n eq_refl). inversion H0.
  unfold bool_in.
  simpl (in_dec cand_decidable b [a]).
  destruct (cand_decidable a b). inversion e.
  auto. auto. destruct d.
  admit. admit. admit.

  destruct c. destruct d. admit.
  simpl. auto. simpl. auto.
  destruct d. admit. admit.
  simpl. auto.
  destruct d. admit. admit. admit.
