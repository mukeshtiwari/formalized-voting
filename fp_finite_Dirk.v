Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.
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

  Lemma eeq_swap : forall (A : Type) (p q : pred A),  pred_eeq p q -> pred_eeq q p.
  Proof.
    intros A p q H. destruct H. split; auto.
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

  (* complement of set *)
  Definition complement {A : Type} p : pred A := fun x => negb (p x).

  (* the empty subset *)
  Definition empty_ss {A: Type} : pred A := fun a => false.

  Lemma empty_ss_subset {A : Type} : forall (p : pred A), pred_subset empty_ss p.
  Proof.
    intros p. unfold pred_subset. intros a H.
    inversion H.
  Qed.

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
    simpl. lia.
    assert (Hp1t: p1 x = false) by apply (not_true_is_false (p1 x) n).
    rewrite Hp1t.
    destruct (bool_dec (p2 x) true). rewrite e. simpl. lia.
    assert (Hp2f: p2 x = false) by apply (not_true_is_false (p2 x) n0).
    rewrite Hp2f. assumption.
  Qed.

  (**************************************)
  (* monotone operators on finite types *)
  (**************************************)

  (* operator on subsets of a type *)
  Definition Op (A: Type) := pred A -> pred A.

  (* dual operator *)
  Definition dual_op {A : Type} (O : Op A) (W : Op A) :=
    forall p : pred A, pred_eeq (O p) (complement (W (complement p))).

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
    replace (n+0)%nat with n. apply subset_refl. lia.
    apply (subset_trans (iter O n empty_ss) (iter O(n+k) empty_ss) (iter O (n + S k) empty_ss)).
    assumption. replace (n + S k)%nat with ((n+k)+1)%nat.
    apply inc_chain. assumption. lia.
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
    lia.
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
    transitivity (card l (iter O 0 empty_ss) + 1)%nat. lia. assumption.
    (* step case *)
    destruct IHn as [Hfix | Hnfix].
    left. simpl. apply op_cong. assumption. assumption.
    assert (pred_eeq (iter O (n+1) empty_ss) (iter O (n+1+1) empty_ss)
            \/ card l (iter O (n + 1 + 1) empty_ss) >= card l (iter O (n + 1) empty_ss) + 1).
    apply (iter_aux O l Hmon Hfin (n + 1)).
    destruct H as [Hl | Hr]. left. replace (S n) with (plus n 1). assumption. lia.
    right. replace (S n) with (plus n 1). lia. lia.
  Qed.


  (* once we have a fixpoint, iterations don't add things *)
  Theorem fp_reached : forall (A : Type) (O : Op A)  (k : nat),
      mon O -> (pred_eeq (iter O k empty_ss) (iter O (k+1) empty_ss)) ->
      forall m, (pred_eeq (iter O k empty_ss) (iter O (k+m) empty_ss)).
  Proof.
    intros A O k Hmon Hiter m.
    induction m as [| m IHm].
    (* m = 0 *)
    replace (plus k 0) with k. apply eeq_refl. lia.
    (* S m *)
    assert (H: pred_eeq (O (iter O k empty_ss)) (O (iter O (k + m) empty_ss))) by
        apply (op_cong O Hmon (iter O k empty_ss) (iter O (plus k m) empty_ss) IHm).
    apply (eeq_trans (iter O k empty_ss) (iter O (k+1) empty_ss) (iter O (k + S m) empty_ss)).
    assumption.
    replace (k + S m)%nat with (S (k+m))%nat. replace (k+1)%nat with (S k). simpl. assumption.
    lia. lia.
  Qed.

  (* trivia about filter *)
  Theorem length_filter : forall (A : Type) (f : A -> bool) (l : list A),
      length (filter f l) <= length l.
  Proof.
    intros A f l. induction l. simpl. lia.
    simpl. destruct (f a). simpl; lia.
    lia.
  Qed.

  (* for a type with at most k elements, we need at most k iterations to reach a fixpoint *)
  Theorem iter_fin {A: Type} (k: nat) (O: (A -> bool) -> (A -> bool)) :
    mon O -> bounded_card A k -> forall n: nat, pred_subset (iter O n empty_ss) (iter O k empty_ss).
  Proof.
    intros Hmon Hboun; unfold bounded_card in Hboun.
    destruct Hboun as [l [Hin Hlen]]. intros n.
    assert (Hle : k < n \/ k >= n) by lia.
    destruct Hle as [Hlel | Hler].
    (* case k < n *)
    destruct (iter_fp O l Hmon Hin k) as [L | R].
    (* case O^k bot = O^k+1 bot *)
    assert (Ht : pred_eeq (iter O k empty_ss) (iter O (k + (n-k)) empty_ss)).
    apply fp_reached. assumption. assumption.
    replace (plus k (n - k)) with n in Ht. destruct Ht as [Ht1 Ht2]. assumption. lia.
    (* case too many elements *)
    unfold card in R.
    assert (Hlen2: length (filter (iter O (k + 1) empty_ss) l) <= length l) by
        apply  (length_filter A (iter O (plus k 1) empty_ss) l).
    unfold ge in R. assert (Hc: k+1 <= k).
    transitivity (length (filter (iter O (k + 1) empty_ss) l)). assumption.
    transitivity (length l). assumption. assumption.
    assert (False). lia. inversion H.
    (* case k >= n *)
    Check inc_chain_trans. 
    replace k with (n + (k-n))%nat.
    apply inc_chain_trans. assumption. lia.
  Qed.

  (* start of greatest fixed point *)
  (* start with all the elements *)
  Definition full_ss {A: Type} : pred A := fun a => true.

  Lemma full_ss_subset {A : Type} : forall (p : pred A), pred_subset p full_ss.
  Proof.
    intros p. unfold pred_subset. intros. reflexivity.
  Qed.

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
    replace (n+0)%nat with n. apply subset_refl. lia.
    apply subset_trans with (q := iter O (n + k) full_ss).
    replace (n + S k)%nat with ((n+k)+1)%nat.
    apply dec_chain. assumption. lia. assumption.
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
    apply pred_filter, dec_chain. assumption. lia.
  Qed.

  (* for finite types, either a fixpoint is reached or the n+1-st iterate + n+1 <=
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
    (* This is really bizzare. lia is not able to solve obvious goal so unfold pred in *
       to change implicit arguments as suggested by jrw*)
    unfold pred in *. lia. apply length_filter. lia.
    destruct IHn as [Hfix | Hnfix].
    left. simpl. apply op_cong. auto. auto.
    assert (pred_eeq (iter O (n + 1 + 1) full_ss) (iter O (n + 1) full_ss) \/
            card l (iter O (n + 1) full_ss) >= card l (iter O (n + 1 + 1) full_ss) + 1).
    apply (iter_aux_dec O l Hmon Hfin (n + 1)).
    destruct H as [Hl | Hr]. left. replace (S n) with (n + 1)%nat. auto. lia.
    right. replace (S n) with (n + 1) %nat. lia. lia.
  Qed.

  (* once we have a greatest fixpoint, iterations don't add things *)
  Theorem fp_reached_gfp : forall (A : Type) (O : Op A)  (k : nat),
      mon O -> (pred_eeq (iter O (k + 1) full_ss) (iter O k full_ss)) ->
      forall m, (pred_eeq (iter O (k + m) full_ss) (iter O k full_ss)).
  Proof.
    intros A O k Hmon Hiter m.
    induction m as [|m IHm].
    replace (k + 0)%nat with k. apply eeq_refl. lia.
    assert (H: pred_eeq (O (iter O (k + m) full_ss)) (O (iter O k full_ss))) by
        apply (op_cong O Hmon (iter O (plus k m) full_ss) (iter O k full_ss) IHm).
    apply (eeq_trans (iter O (k + S m) full_ss) (iter O (k+1) full_ss) (iter O k full_ss)).
    replace (k + S m)%nat with (1 + (k + m))%nat. replace (k + 1)%nat with (1 + k)%nat.
    simpl. assumption. lia. lia. auto.
  Qed.

  (* for a type with at most k elements, we need at most k iterations to reach a fixpoint *)
  Theorem iter_fin_gfp {A: Type} (k: nat) (O: (A -> bool) -> (A -> bool)) :
    mon O -> bounded_card A k -> forall n: nat, pred_subset (iter O k full_ss) (iter O n full_ss).
  Proof.
    intros Hmon Hboun; unfold bounded_card in Hboun.
    destruct Hboun as [l [Hin Hlen]]. intros n.
    assert (Hle : k < n \/ k >= n) by lia.
    destruct Hle as [Hlel | Hler].
    (* case k < n *)
    destruct (iter_fp_gfp O l Hmon Hin k) as [L | R].
    assert (Ht : pred_eeq (iter O (k + (n - k)) full_ss) (iter O k full_ss)).
    apply fp_reached_gfp. assumption. assumption.
    replace (k + (n - k))%nat with n in Ht. destruct Ht as [Ht1 Ht2]. assumption.
    lia. lia.
    replace k with (n + (k-n))%nat. apply dec_chain_trans. assumption. lia.
  Qed.


  Definition least_fixed_point (A : Type) (l : list A) (H : forall a : A, In a l)
             (V : Op A) (Hmon : mon V) :=  iter V (length l) empty_ss.

  Definition greatest_fixed_point (A : Type) (l : list A) (H : forall a : A, In a l)
             (O : Op A) (Hmon : mon O) := iter O (length l) full_ss.

  Definition fixed_point (A : Type) (O : Op A) (f : pred A) :=
    pred_eeq f (O f).

  Theorem least_fixed_point_is_fixed_point : forall (A : Type) (l : list A) (H : forall a, In a l)
                                               (O : Op A) (Hmon : mon O),
      fixed_point A O (least_fixed_point A l H O Hmon).
  Proof.
    intros A l H O Hmon. unfold fixed_point. split.
    unfold least_fixed_point.
    replace (O (iter O (length l) empty_ss)) with  (iter O (length l + 1) empty_ss).
    apply inc_chain. assumption. replace (length l + 1)%nat with (S (length l)).
    reflexivity. lia. unfold least_fixed_point.
    replace (O (iter O (length l) empty_ss)) with  (iter O (length l + 1) empty_ss).
    apply iter_fin. assumption. unfold bounded_card. exists l. split. assumption.
    lia.  replace (length l + 1)%nat with (S (length l)). reflexivity. lia.
  Qed.

  Lemma greatest_fixed_point_is_fixed_point :
     forall (A : Type) (l : list A) (H : forall a, In a l)
       (O : Op A) (Hmon : mon O), fixed_point A O (greatest_fixed_point A l H O Hmon).
  Proof.
    intros A l H O Hmon. split. unfold greatest_fixed_point.
    replace (O (iter O (length l) full_ss)) with (iter O (length l + 1) full_ss).
    apply iter_fin_gfp. assumption. unfold bounded_card. exists l. intuition.
    replace (length l + 1)%nat with (S (length l)). reflexivity. lia.
    unfold greatest_fixed_point.
    replace (O (iter O (length l) full_ss)) with (iter O (length l + 1) full_ss).
    apply dec_chain. assumption. replace (length l + 1)%nat with (S (length l)).
    simpl. reflexivity. lia.
  Qed.
   
  Lemma fixed_point_temp_for_now : forall (A : Type) (O : Op A) (Hmon : mon O) (f : pred A),
      fixed_point A O f -> forall n, pred_subset (iter O n empty_ss) f.
  Proof.
    intros A O Hmon f Hfix.
    induction n. simpl. apply empty_ss_subset.
    apply (subset_trans (iter O (S n) empty_ss) (O f) f).
    simpl. apply Hmon. assumption. unfold fixed_point in Hfix.
    unfold pred_eeq in Hfix. intuition.
  Qed.

  Lemma fixed_point_temp_for_now_gfp : forall (A : Type) (O : Op A) (Hmon : mon O) (f : pred A),
      fixed_point A O f -> forall n, pred_subset f (iter O n full_ss).
  Proof.
    intros A O Hmon f Hfix. unfold fixed_point in Hfix.
    induction n. simpl. apply full_ss_subset.
    apply (subset_trans f (O f) (iter O (S n) full_ss)).
    unfold pred_eeq in Hfix. intuition. simpl. apply Hmon. assumption.
  Qed.
      
  Lemma least_fixed_point_is_least : forall (A : Type) (l : list A) (H : forall a, In a l)
                                       (O : Op A) (Hmon : mon O) (f : pred A),
      fixed_point A O f -> pred_subset (least_fixed_point A l H O Hmon) f.
  Proof.
    intros A l H O Hmon f Hfix. unfold least_fixed_point.
    apply fixed_point_temp_for_now; assumption.
  Qed.

  Lemma greatest_fixed_point_is_greatest :
    forall (A : Type) (l : list A) (H : forall a, In a l)
      (O : Op A) (Hmon : mon O) (f : pred A),
      fixed_point A O f -> pred_subset f (greatest_fixed_point A l H O Hmon).
  Proof.
    intros A l H O Hmon f Hfix. unfold greatest_fixed_point.
    apply fixed_point_temp_for_now_gfp; assumption.
  Qed.
  
  Definition lfp {A : Type} (p : pred A) (O : Op A) :=
    fixed_point A O p /\ forall (q : pred A), (fixed_point A O q -> pred_subset p q).

  Definition gfp {A : Type} (p : pred A) (O : Op A) :=
    fixed_point A O p /\ forall (q : pred A), (fixed_point A O q -> pred_subset q p).

  Lemma iter_lfp : forall (A : Type) (l : list A) (H : forall a, In a l)
                     (O : Op A) (Hmon : mon O), lfp (least_fixed_point A l H O Hmon) O.
  Proof.
    intros A l H O Hmon. unfold lfp. split.
    apply least_fixed_point_is_fixed_point.
    intros q Hf. apply least_fixed_point_is_least. assumption.
  Qed.

  
  Lemma complement_id : forall (A : Type) (p : pred A),
      pred_eeq (complement (complement p)) p.
  Proof.
    unfold pred_eeq. unfold pred_subset. unfold complement. intros a p.
    split. intros a0 H. rewrite <- negb_involutive_reverse in H. assumption.
    intros a0 H. rewrite <- negb_involutive_reverse. assumption.
  Qed.

  (*
  Lemma complement_id : forall (A : Type) (p : pred A),
      complement (complement p) = p.
  Admitted.
   *)

  Lemma eeq_complement : forall (A : Type) (p q : pred A),
      pred_eeq p q -> pred_eeq (complement p) (complement q).
  Proof.
    intros A p q H. unfold pred_eeq in *. unfold pred_subset in *.
    destruct H. unfold complement. split. intros a Hn. apply negb_true_iff.
    apply negb_true_iff in Hn. destruct (q a) eqn:Ht. specialize (H0 a Ht).
    congruence. reflexivity.
    intros a Hn. apply negb_true_iff. apply negb_true_iff in Hn.
    destruct (p a) eqn:Ht. specialize (H a Ht). congruence.
    reflexivity.
  Qed.

  Lemma subset_comp : forall (A : Type) (p q : pred A),
      pred_subset (complement p) q -> pred_subset (complement q) p.
  Proof.
    intros a p q H. unfold pred_subset in *. unfold complement in *.
    intros a0 H1. apply negb_true_iff in H1. destruct (p a0) eqn:Ht.
    reflexivity. specialize (H a0). rewrite negb_true_iff in H. apply H in Ht.
    congruence.
  Qed.



  (*
  Lemma complement_id_1 : forall (A : Type) (p : pred A),
      pred_eeq p 

  
  Lemma operator_equality : forall (A : Type) (O W : Op A) (H : dual_op O W) (p q : pred A),
      lfp p O -> gfp q W -> pred_eeq p (complement q).
  Proof.
   intros A O W H p q H1 H2.
   unfold dual_op in *. unfold lfp in *. unfold gfp in *.
   destruct H1, H2. unfold fixed_point in *.
   specialize (eeq_trans _ _ _ H0 (H p)); intros.
   pose proof (eeq_complement _ _ _ H4). rewrite complement_id_1 in H5.
   pose proof  (H3 _ H5).
   pose proof H (complement q). specialize (eeq_complement _ _ _ H7); intros.
   rewrite complement_id_1 in H8. rewrite complement_id_1 in H8.
   apply eeq_swap in H8. specialize (eeq_trans _ _ _ H2 H8); intros.
   specialize (eeq_complement _ _ _ H9); intros. rewrite complement_id_1 in H10.
   apply H1 in H10. split.  assumption. apply subset_comp in H6. assumption.
 Qed.
   *)

  Lemma complement_underW : forall (A : Type) (W : Op A) (H : mon W) (p q : pred A),
      pred_eeq p (W (complement (complement q))) -> pred_eeq p (W q).
  Proof.
    intros A W Hmon p q H.
    assert (Ht : pred_eeq (W (complement (complement q))) (W q)). 
    apply op_cong. assumption. apply complement_id.
    specialize (eeq_trans _ _ _ H Ht); intros. assumption.
  Qed.
  
  Lemma operator_equality : forall (A : Type) (O W : Op A) (Hw : mon W)
                              (H : dual_op O W) (p q : pred A),
      lfp p O -> gfp q W -> pred_eeq p (complement q).
  Proof.
    intros A O W Hw H p q H1 H2.
    unfold dual_op in *. unfold lfp in *. unfold gfp in *.
    destruct H1, H2. unfold fixed_point in *.
    specialize (eeq_trans _ _ _ H0 (H p)); intros.
    pose proof (eeq_complement _ _ _ H4).
    specialize (eeq_trans _ _ _ H5 (complement_id _ _)); intros.
    pose proof (H3 _ H6). pose proof H (complement q).
    specialize (eeq_complement _ _ _ H8); intros.
    specialize (eeq_trans _ _ _ H9 (complement_id _ _)); intros.
    assert (Ht : pred_eeq (complement (O (complement q))) (W (complement (complement q))) ->
                 pred_eeq (complement (O (complement q))) (W q)).
    apply complement_underW. assumption.    
    apply eeq_swap in Ht. specialize (eeq_trans _ _ _ H2 Ht); intros.
    specialize (eeq_complement _ _ _ H11); intros.
    specialize (eeq_trans _ _ _ H12 (complement_id _ _)); intros.
    apply H1 in H13. split. assumption. apply subset_comp in H7. assumption.
    assumption.
  Qed.

  Definition coclosed (A : Type) (O : Op A) (p : pred A) :=
    pred_subset p (O p).

  Lemma fixed_point_is_coclosed : forall (A : Type) (O : Op A) (p : pred A),
      fixed_point A O p -> coclosed A O p.
  Proof.
    intros A O p H. unfold fixed_point in H.
    unfold coclosed. unfold pred_eeq in H. firstorder.
  Qed.
  
End Fixpoints.
