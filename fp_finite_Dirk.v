Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Import ListNotations.


Module Fixpoints.

  
  (****************************************************)
  (* boolean predicates on types and basic properties *)
  (****************************************************)

  (* boolean predicates *)
  Definition pred (A: Type) := A -> bool.

  (* subset relation on boolean predicates *)
  Definition pred_subset {A: Type} (p1 p2: pred A) :=
    forall a: A, p1 a = true -> p2 a = true.

  (* extensional equality of boolean predicates *)
  Definition pred_eeq {A: Type} (p1 p2: pred A) :=
    pred_subset p1 p2 /\ pred_subset p2 p1.

  (* subset is reflexive *)
  Lemma subset_refl {A: Type} (p: pred A) : pred_subset p p.
    Proof.
    unfold pred_subset. intro a. auto.
  Qed.

  (* equality is reflexive *)
  Lemma eeq_refl {A: Type} (p: pred A) : pred_eeq p p.
  Proof.
    unfold pred_eeq. split; apply subset_refl.
  Qed.

  (* subset is transitive *)
  Lemma subset_trans {A: Type} (p q r: pred A):
    pred_subset p q -> pred_subset q r -> pred_subset p r.
  Proof.
    intros Hpq Hqr. unfold pred_subset in Hpq, Hqr. unfold pred_subset.
    intro a. specialize (Hpq a). specialize (Hqr a).
    intro H. apply Hqr, Hpq. assumption.
  Qed. 

  (* equality is transitive *)
  Lemma eeq_trans {A: Type} (p q r: pred A) :
    pred_eeq p q -> pred_eeq q r -> pred_eeq p r.
  Proof.
    intros  Hpq Hqr.
    unfold pred_eeq in Hpq, Hqr. destruct  Hpq as [Hpq1 Hpq2].
    destruct Hqr as [Hqr1 Hqr2].
    unfold pred_eeq. split. 
    apply (subset_trans p q r); assumption.
    apply (subset_trans r q p); assumption.
  Qed.

  (* the empty subset *)
  Definition empty_ss {A: Type} : pred A := fun a => false.

  (* equality on boolean predicates on a finite type is decidable *)
  Lemma pred_eq_dec_aux {A: Type} (l: list A) :
    forall (p1 p2: pred A), {forall a, In a l -> p1 a = p2 a} + {~(forall a, In a l -> p1 a = p2 a)}.
  Proof.
    induction l as [| x xs IHxs].
    (* nil case *)
    intros p1 p2. left.
    intros a Hin. inversion Hin.
    (* list of the form x:xs *)
    intros p1 p2.
    (* case distinction on whether p1 x = p2 x *)
    Require Import Coq.Bool.Bool.
    destruct (bool_dec (p1 x) (p2 x)) as [H12eqx | H12neqx].
    (* case p1 x = p2 x *)
    (* case distinction on whether p1 and p2 agree on xs *)
    destruct (IHxs p1 p2) as [H12eqxs | H12neqxs].
    (* case where p1 and p2 agree on xs *)
    left. intros a Hin. 
    apply in_inv in Hin. destruct Hin as [Hx | Hxs].
    rewrite Hx in H12eqx. assumption.
    apply H12eqxs. assumption.
    (* p1 x = p2 x but p1 and p2 don't agree on xs *)
    right.
    intro H. apply H12neqxs. intro a. specialize (H a). intro  Hin.
    apply H. simpl.   right. assumption.
    (* case where p1 x <> p2 x *)
    right.
    intro H. apply H12neqx. specialize (H x). apply H. simpl. left. trivial.
  Qed.

  (* decidability for finite types *)
  Lemma pred_eq_dec {A: Type} (l: list A) :
    (forall a: A, In a l) ->
    forall (p1 p2: pred A), {pred_eeq p1 p2} + {~(pred_eeq p1 p2)}.
  Proof.
    intros Hin p1 p2.
    destruct (pred_eq_dec_aux l p1 p2) as [Heq | Hneq].
    left.
    unfold pred_eeq. split. unfold pred_subset. intro a. 
    specialize (Heq a (Hin a)).
    rewrite Heq. auto.
    unfold pred_subset. intro a.
    specialize (Heq a (Hin a)).
    rewrite Heq. auto.
    (* case where p1 and p2 are different *)
    right. intro H. apply Hneq.
    unfold pred_eeq in H. destruct H as [H1 H2].
    unfold pred_subset in H1. unfold pred_subset in H2. intros a Hin'.
    (* case analysis on p1 a, p2 a *)
    destruct (bool_dec (p1 a) true) as [Hp1t | Hp1f].
    (* case p1 a = true *)
    assert (H: p2 a = true). apply H1. assumption. congruence.
    (* case p1 a = false *)
    assert (Hp1: p1 a = false) by  apply (not_true_is_false (p1 a) Hp1f).
    destruct (bool_dec (p2 a) true) as [Hp2t | Hp2f].
    (* case p2 a = true *)
    specialize (H2 a Hp2t). contradict Hp1f. assumption.
    (* case p2 a = false *)
    assert (Hp2: p2 a = false) by apply (not_true_is_false (p2 a) Hp2f). congruence.
  Qed.  

  (* if two predicates are subsets but not equal, the larger adds an elt *)
  Lemma new_elt_aux {A: Type} (p1 p2: pred A)  (l: list A) :
    pred_subset p1 p2 -> 
    (~ (forall a: A, In a l -> p1  a = p2  a)) ->
    exists a: A, p1  a = false /\ p2 a = true.
  Proof.
    unfold pred.
    intros Hss Hneq.
    induction l as [| x xs IHxs].
    contradict Hneq. intros a Hin.
    inversion Hin.
    (* l = x:xs *)
    destruct (bool_dec (p1 x) (p2 x)).
    (* case where p1 x = p2 x *)
    (* p1 and p2 must disagree on xs *)
    apply IHxs. intro H. apply Hneq.
    intros a Hin.
    apply in_inv in Hin.
    destruct Hin as [Hxa | Haxs]. congruence.
    apply (H a). assumption.
    (* case where p1 and p2 disagree on x *)
    exists x. destruct (bool_dec (p1 x) true).
    (* case where p1 x = true *)
    assert (Hp2: p2 x = false). destruct (bool_dec (p2 x) false).
    assumption.
    rewrite e in n.
    apply not_true_iff_false. auto. unfold pred_subset in Hss. specialize (Hss x).
    specialize (Hss e).
    rewrite e in n. congruence.
    (* case where p1x is not true, i.e. false *)
    assert (Hp1: p1 x = false). apply not_true_iff_false. assumption.
    rewrite Hp1 in n.
    split. assumption.  apply not_false_is_true.  intro H.
    symmetry in H. apply n. assumption.
  Qed.

  (* new_elt for finite types *)
  Lemma new_elt {A: Type} (p1 p2: pred A) (l: list A) :
    (forall a: A, In a l) ->
    pred_subset p1 p2 -> ~(pred_eeq p1 p2) -> 
    exists a: A, p1  a = false /\ p2 a = true.
  Proof.
    intros Hfin Hss Hneq.
    apply (new_elt_aux p1 p2 l Hss).
    intro H.  unfold pred_eeq in Hneq. apply Hneq. 
    split. unfold pred_subset.
    intros a Hp1. specialize (H a (Hfin a)).  congruence.
    unfold pred_subset.
    intros a Hp2. specialize (H a (Hfin a)). congruence.
  Qed.

  (* additivity of filter *)
  Lemma filter_app {A: Type} (l1 l2: list A) (f: A -> bool) :
    filter f (l1 ++ l2) = (filter f l1) ++ (filter f l2).
  Proof.
    induction l1. auto.
    simpl. destruct (f a). simpl. rewrite IHl1. auto.
    assumption.
  Qed.

  (* length is compatible with subset inclusion *)
  Lemma pred_filter {A: Type} (p1 p2: pred A) (l: list A) :
    pred_subset p1 p2 -> length (filter p1 l) <= length (filter p2 l).
  Proof.
    intro Hss. induction l as [| x xs IHxs].
    simpl. auto.
    simpl. destruct (bool_dec (p1 x) true).
    rewrite e. simpl.
    unfold pred_subset in Hss. specialize (Hss x e). rewrite Hss.
    simpl. omega.
    assert (Hp1t: p1 x = false) by apply (not_true_is_false (p1 x) n).
    rewrite Hp1t.
    destruct (bool_dec (p2 x) true). rewrite e. simpl. omega.
    assert (Hp2f: p2 x = false) by apply (not_true_is_false (p2 x) n0).
    rewrite Hp2f. assumption.
  Qed.

  (**************************************)
  (* monotone operators on finite types *)
  (**************************************)

  (* operator on subsets of a type *)
  Definition Op (A: Type) := pred A -> pred A.

  (* monotonicity *)
  Definition mon {A: Type} (O:Op A) :=
    forall (p1 p2: pred A), pred_subset p1 p2 -> pred_subset (O p1) (O p2).

  (* cardinality of a type bounded by a natural number *)
  Definition bounded_card (A: Type) (n: nat) := 
    exists l, (forall a: A, In a l) /\ length l <= n.

  (* iterate an endofunction on a type *)
  Fixpoint iter {A: Type} (f: A -> A) (n: nat) (a: A) :=
    match n with
    | 0 => a
    | S m => f (iter f m a)
    end.

  (* number of elements in a list that satisfy given predicate *)
  Definition card {A: Type} (l: list A) (p: A -> bool) := length (filter p l).

  (* the iterates of a monotone operator form an increasing chain *)
  Lemma inc_chain {A: Type} (O: Op A) : mon O ->
    forall n: nat, pred_subset (iter O n empty_ss) (iter O (n+1) empty_ss).
  Proof.
    intros Hmon n.
    induction n.
    (* base case: n = 0 *)
    simpl.
    unfold pred_subset.
    intro a. unfold empty_ss. intro Hf. inversion Hf.
    (* step case *)
    simpl. unfold mon in Hmon. apply Hmon. assumption.
  Qed.

  (* combined with transitivity *)
  Lemma inc_chain_trans {A: Type} (O: Op A): mon O ->
    forall (n k: nat), pred_subset (iter O n empty_ss) (iter O (n+k) empty_ss).
  Proof.
    intros Hmon n k. induction k as [| k IHk].
    (* k = 0 *)
    replace (n+0)%nat with n. apply subset_refl. omega.
    apply (subset_trans (iter O n empty_ss) (iter O(n+k) empty_ss) (iter O (n + S k) empty_ss)).
    assumption. replace (n + S k)%nat with ((n+k)+1)%nat.
    apply inc_chain. assumption. omega.
  Qed.
  
  (* the operator is congruential on predicates *)
  Lemma op_cong {A: Type} (O: Op A) : mon O -> forall p1 p2: pred A,
        pred_eeq p1 p2 -> pred_eeq (O p1) (O p2).
  Proof.
    intros Hmon p1 p2 Heq. unfold pred_eeq. destruct Heq as [H1 H2]. split.
    unfold mon in Hmon. apply (Hmon p1 p2 H1). apply (Hmon p2 p1 H2).
  Qed.

  (* for finite types, either a fixpoint is reached or the cardinality of the iterate increases *)
  Theorem  iter_aux {A: Type} (O: (A -> bool) -> (A -> bool)) (l: list A):
    mon O -> (forall a: A, In a l) ->
   forall n: nat, (pred_eeq (iter O n empty_ss) (iter O (n+1) empty_ss))  \/
           (card l (iter O (n+1) empty_ss) >= card l (iter O n empty_ss) + 1).
  Proof.
    intros Hmon Hfin n.
    destruct (pred_eq_dec l Hfin (iter O n empty_ss) (iter O (n+1) empty_ss)) as [Heq | Hneq].
    (* O^0 empty  = O^1 empty *)
    left. assumption.
    (* case where O^0 empty != O^1 empty *)
    right.
    (* we know: O^0 emty != O^1 empty but by monotonicity, have O^0 empty (subset of) O^1 empty. *)
    assert (Hne: exists a, iter O n empty_ss a = false /\ iter O (n+1) empty_ss a = true).
    apply (new_elt (iter O n empty_ss) (iter O (n+1) empty_ss) l Hfin).
    apply (inc_chain O Hmon n). assumption.
    destruct Hne as [a Hne].
    assert (Hsplit:  exists l1 l2, l = l1++a::l2). apply in_split. apply Hfin.
    destruct Hsplit as [l1 [l2 Hsplit]].
    unfold card.
    rewrite Hsplit, filter_app, filter_app.
    destruct Hne as [Hnef Hnet].
    rewrite app_length, app_length. simpl.
    rewrite Hnef, Hnet. simpl.
    Check pred_filter.
    assert (Hl1:  length (filter (iter O n empty_ss) l1) <=
                  length (filter (iter O (n+1) empty_ss) l1)).
    apply pred_filter. apply inc_chain. assumption.
    assert (Hl2: length (filter (iter O n empty_ss) l2) <=
                 length (filter (iter O (n+1) empty_ss) l2)).
    apply pred_filter, inc_chain. assumption.
    omega.
  Qed.

  (* for finite types, either a fixpoint is reached or the n+1-st iterate has >= n+1 elements *)
  Theorem  iter_fp {A: Type} (O: Op A) (l: list A):
    mon O -> (forall a: A, In a l) ->
    forall (n : nat), (pred_eeq (iter O n empty_ss) (iter O (n+1) empty_ss)) \/
               card l (iter O (n+1) empty_ss) >= (n+1).
  Proof.
    intros Hmon Hfin n.  induction n.
    destruct (iter_aux O l Hmon Hfin 0).
    left; assumption.
    right. unfold ge; unfold ge in H.
    transitivity (card l (iter O 0 empty_ss) + 1)%nat. omega. assumption.
    (* step case *)
    destruct IHn as [Hfix | Hnfix].
    left. simpl. apply op_cong. assumption. assumption.
    assert (pred_eeq (iter O (n+1) empty_ss) (iter O (n+1+1) empty_ss)
            \/ card l (iter O (n + 1 + 1) empty_ss) >= card l (iter O (n + 1) empty_ss) + 1).
    apply (iter_aux O l Hmon Hfin (n + 1)).
    destruct H as [Hl | Hr]. left. replace (S n) with (plus n 1). assumption. omega.
    right. replace (S n) with (plus n 1). omega. omega.
  Qed.
    

  (* once we have a fixpoint, iterations don't add things *)
  Theorem fp_reached : forall (A : Type) (O : Op A)  (k : nat),
      mon O -> (pred_eeq (iter O k empty_ss) (iter O (k+1) empty_ss)) ->
      forall m, (pred_eeq (iter O k empty_ss) (iter O (k+m) empty_ss)).
  Proof.
    intros A O k Hmon Hiter m.
    induction m as [| m IHm].
    (* m = 0 *)
    replace (plus k 0) with k. apply eeq_refl. omega.
    (* S m *)
    assert (H: pred_eeq (O (iter O k empty_ss)) (O (iter O (k + m) empty_ss))) by 
        apply (op_cong O Hmon (iter O k empty_ss) (iter O (plus k m) empty_ss) IHm).
    apply (eeq_trans (iter O k empty_ss) (iter O (k+1) empty_ss) (iter O (k + S m) empty_ss)).
    assumption.
    replace (k + S m)%nat with (S (k+m))%nat. replace (k+1)%nat with (S k). simpl. assumption.
    omega. omega.
  Qed.

  (* trivia about filter *)  
  Theorem length_filter : forall (A : Type) (f : A -> bool) (l : list A),
      length (filter f l) <= length l.
  Proof.
    intros A f l. induction l. simpl. omega.
    simpl. destruct (f a). simpl; omega.
    omega.
  Qed.
  
  (* for a type with at most k elements, we need at most k iterations to reach a fixpoint *)
  Theorem iter_fin {A: Type} (k: nat) (O: (A -> bool) -> (A -> bool)) :
    mon O -> bounded_card A k -> forall n: nat, pred_subset (iter O n empty_ss) (iter O k empty_ss).
  Proof.
    intros Hmon Hboun; unfold bounded_card in Hboun.
    destruct Hboun as [l [Hin Hlen]]. intros n.
    assert (Hle : k < n \/ k >= n) by omega.    
    destruct Hle as [Hlel | Hler].
    (* case k < n *)
    destruct (iter_fp O l Hmon Hin k) as [L | R].
    (* case O^k bot = O^k+1 bot *)
    assert (Ht : pred_eeq (iter O k empty_ss) (iter O (k + (n-k)) empty_ss)).
    apply fp_reached. assumption. assumption.
    replace (plus k (n - k)) with n in Ht. destruct Ht as [Ht1 Ht2]. assumption. omega.
    (* case too many elements *)
    unfold card in R. 
    assert (Hlen2: length (filter (iter O (k + 1) empty_ss) l) <= length l) by
        apply  (length_filter A (iter O (plus k 1) empty_ss) l).
    unfold ge in R. assert (Hc: k+1 <= k).
    transitivity (length (filter (iter O (k + 1) empty_ss) l)). assumption.
    transitivity (length l). assumption. assumption. 
    assert (False). omega. inversion H.
    (* case k >= n *)
    Check inc_chain_trans.
    replace k with (n + (k-n))%nat.
    apply inc_chain_trans. assumption. omega.
  Qed.

  (* start of greatest fixed point *)
  (* start with all the elements *)
  Definition full_ss {A: Type} : pred A := fun a => true.

   (* the iterates of a monotone operator form an decreasing chain *)
  Lemma dec_chain {A: Type} (O: Op A) :
    mon O -> forall n: nat, pred_subset (iter O (n + 1) full_ss) (iter O n full_ss).
  Proof.
    intros Hmon n. induction n.
    (* base case: n = 0 *)
    simpl. unfold pred_subset.
    intro a. unfold full_ss. intro Hf. auto.
    (* step case *)
    simpl. unfold mon in Hmon. apply Hmon. assumption.
  Qed.

  (* combined with transitivity *)
  Lemma dec_chain_trans {A: Type} (O: Op A): mon O ->
    forall (n k: nat), pred_subset (iter O (n + k) full_ss) (iter O n full_ss).
  Proof.
    intros Hmon n k. induction k as [| k IHk].
    (* k = 0 *)
    replace (n+0)%nat with n. apply subset_refl. omega.
    apply subset_trans with (q := iter O (n + k) full_ss). 
    replace (n + S k)%nat with ((n+k)+1)%nat.
    apply dec_chain. assumption. omega. assumption.
  Qed.

  
  (* for finite types, either a fixpoint is reached or 
     the cardinality of the iterate decrease *)
  Theorem iter_aux_dec {A: Type} (O: (A -> bool) -> (A -> bool)) (l: list A):
    mon O -> (forall a: A, In a l) ->
    forall n: nat, (pred_eeq (iter O (n + 1) full_ss) (iter O n full_ss))  \/
            (card l (iter O n full_ss) >= card l (iter O (n + 1) full_ss) + 1).
  Proof.
    intros Hmon Hfin n.
    destruct (pred_eq_dec l Hfin (iter O (n + 1) full_ss) (iter O n full_ss)) as [Heq | Hneq].
    left. assumption.
    right.
    assert (Hne: exists a, iter O (n + 1) full_ss a = false /\ iter O n full_ss a = true).
    apply (new_elt (iter O (n + 1) full_ss) (iter O n full_ss) l Hfin).
    apply (dec_chain O Hmon n). assumption.
    destruct Hne as [a Hne].
    assert (Hsplit: exists l1 l2, l = l1++a::l2). apply in_split. apply Hfin.
    destruct Hsplit as [l1 [l2 Hsplit]]. unfold card.
    rewrite Hsplit, filter_app, filter_app.
    destruct Hne as [Hnef Hnet]. rewrite app_length, app_length. simpl.
    rewrite Hnef, Hnet. simpl.
    assert (Hl1:  length (filter (iter O (n + 1) full_ss) l1) <=
                  length (filter (iter O n full_ss) l1)).
    apply pred_filter, dec_chain. assumption.
    assert (Hl2: length (filter (iter O (n + 1) full_ss) l2) <=
                 length (filter (iter O n full_ss) l2)).
    apply pred_filter, dec_chain. assumption. omega.
  Qed.

  (* for finite types, either a fixpoint is reached or the n+1-st iterate +  n+1 <= 
    length l elements *)
  Theorem  iter_fp_gfp {A: Type} (O: Op A) (l: list A):
    mon O -> (forall a: A, In a l) ->
    forall (n : nat), (pred_eeq (iter O (n + 1) full_ss) (iter O n full_ss)) \/
               (card l (iter O (n+1) full_ss) + (n + 1)) <= length l.
  Proof.
    intros Hmon Hfin n. induction n.
    destruct (iter_aux_dec O l Hmon Hfin 0).
    left. assumption.
    right. replace (0 + 1)%nat with 1 in *.
    transitivity (card l (iter O 0 full_ss))%nat.
    (* This is really bizzare. Omega is not able to solve obvious goal so unfold pred in *
       to change implicit arguments as suggested by jrw*)
    unfold pred in *. omega. apply length_filter. omega.
    destruct IHn as [Hfix | Hnfix].
    left. simpl. apply op_cong. auto. auto.
    
    assert (pred_eeq (iter O (n + 1 + 1) full_ss) (iter O (n + 1) full_ss) \/
            card l (iter O (n + 1) full_ss) >= card l (iter O (n + 1 + 1) full_ss) + 1).
    apply (iter_aux_dec O l Hmon Hfin (n + 1)).
    destruct H as [Hl | Hr]. left. replace (S n) with (n + 1)%nat. auto. omega.
    right. replace (S n) with (n + 1) %nat. omega. omega.
  Qed.


  
End Fixpoints.    


