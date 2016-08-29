Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Import ListNotations.


Section Fixpoints.

  Definition pred_subset {A: Type} (p1 p2: A -> bool) :=
    forall a: A, p1 a = true -> p2 a = true.

  Definition mon {A: Type} (O: (A -> bool) -> (A -> bool)) :=
    forall (p1 p2: A -> bool), pred_subset p1 p2 -> pred_subset (O p1) (O p2).

  Definition bounded_card (A: Type) (n: nat) := exists l, (forall a: A, In a l) /\ length l <= n.

  Fixpoint iter {A: Type} (f: A -> A) (n: nat) (a: A) :=
    match n with
    | 0 => a
    | S m => f (iter f m a)
    end.

  Definition nil_pred {A: Type} : A -> bool := fun a => false.

  Definition card {A: Type} (l: list A) (p: A -> bool) := length (filter p l).

  Lemma increasing {A: Type} (O: (A -> bool) -> (A -> bool)) :
    mon O -> forall n: nat, pred_subset (iter O n nil_pred) (iter O (n+1) nil_pred).
  Proof.
    intros Hmon n.
    induction n.
    (* base case: n = 0 *)
    simpl.
    unfold pred_subset.
    intro a. unfold nil_pred. simpl. intro Hf. inversion Hf.
    (* step case *)
    simpl. unfold mon in Hmon. apply Hmon. assumption.
  Qed.

  (* equality on boolean predicates on a finite type is decidable *)
  Lemma pred_eq_dec_aux {A: Type} (l: list A) :
    forall (p1 p2: A -> bool), {forall a, In a l -> p1 a = p2 a} + {~(forall a, In a l -> p1 a = p2 a)}.
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
    rewrite -> Hx in H12eqx. assumption.
    apply H12eqxs. assumption.
    (* p1 x = p2 x but p1 and p2 don't agree on xs *)
    right.
    intro H. apply H12neqxs. intro a. specialize (H a). intro  Hin. apply H. simpl.   right. assumption.
    (* case where p1 x <> p2 x *)
    right.
    intro H. apply H12neqx. specialize (H x). apply H. simpl. left. trivial.
  Qed.

  Lemma pred_eq_dec {A: Type} (l: list A) :
    (forall a: A, In a l) ->
    forall (p1 p2: A -> bool), {forall a, p1 a = p2 a} + {~(forall a,  p1 a = p2 a)}.
  Proof.
    intros Hcov p1 p2.
    destruct (pred_eq_dec_aux l p1 p2) as [Heq | Hneq].
    (* case where p1 and p2 are equal *)
    left.
    intro a. apply Heq. apply (Hcov a).
    (* case where p1 and p2 are different *)
    right. intro H. apply Hneq. intros a Hin. apply (H a).
  Qed.

  Lemma new_elt_aux {A: Type} (p1 p2: A -> bool)  (l: list A) :
    pred_subset p1 p2 ->
    (~ (forall a: A, In a l -> p1  a = p2  a)) ->
    exists a: A, p1  a = false /\ p2 a = true.
  Proof.
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
    destruct Hin as [Hxa | Haxs].
    rewrite <- Hxa. assumption.
    apply (H a). assumption.
    (* case where p1 and p2 disagree on x *)
    exists x. destruct (bool_dec (p1 x) true).
    (* case where p1 x = true *)
    assert (Hp2: p2 x = false). destruct (bool_dec (p2 x) false).
    assumption.
    rewrite -> e in n.
    apply not_true_iff_false. auto. unfold pred_subset in Hss. specialize (Hss x). specialize (Hss e).
    rewrite -> e in n. symmetry in Hss. unfold not in n. apply n in Hss. inversion Hss.
    (* case where p1x is not true, i.e. false *)
    assert (Hp1: p1 x = false). apply not_true_iff_false. assumption.
    rewrite -> Hp1 in n.
    split. assumption.  apply not_false_is_true.  intro H.
    symmetry in H. apply n. assumption.
  Qed.

  Lemma new_elt {A: Type} (p1 p2: A -> bool) (l: list A) :
    (forall a: A, In a l) ->
    pred_subset p1 p2 ->
    (~ (forall a: A, p1  a = p2  a)) ->
    exists a: A, p1  a = false /\ p2 a = true.
  Proof.
    intros Hfin Hss Hneq.
    Check new_elt_aux.
    apply (new_elt_aux p1 p2 l Hss).
    intro H. apply Hneq. intro a.
    specialize (Hfin a). specialize (H a). apply H. assumption.
  Qed.

  Lemma filter_app {A: Type} (l1 l2: list A) (f: A -> bool) : filter f (l1 ++ l2) = (filter f l1) ++ (filter f l2).
  Proof.
    induction l1. auto.
    simpl. destruct (f a). simpl. rewrite IHl1. auto.
    assumption.
  Qed.

  Theorem  iter_aux {A: Type} (O: (A -> bool) -> (A -> bool)) (l: list A):
    mon O ->
    (forall a: A, In a l) ->
    forall n: nat, (forall a: A, iter O n nil_pred a = true <-> iter O (n+1) nil_pred a = true) \/
            card l (iter O (n+1) nil_pred) >= card l (iter O n nil_pred) + 1.
  Proof.
    intros Hmon Hfin n.
    destruct (pred_eq_dec l Hfin (iter O n nil_pred) (iter O (n+1) nil_pred)) as [Heq | Hneq].
    (* O^0 empty  = O^1 empty *)
    left.
    intro a. split. intro H0. specialize (Heq a). rewrite <- Heq. assumption.
    intro H1. specialize (Heq a). rewrite -> Heq. assumption.
    (* case where O^0 empty != O^1 empty *)
    right.
    (* we know: O^0 emty != O^1 empty but by monotonicity, have O^0 empty (subset of) O^1 empty. *)
    assert (Hne: exists a, iter O n nil_pred a = false /\ iter O (n+1) nil_pred a = true).
    Check new_elt.
    apply (new_elt (iter O n nil_pred) (iter O (n+1) nil_pred) l Hfin).
    Check increasing.
    apply (increasing O Hmon n). assumption.
    destruct Hne as [a Hne].

    assert (Hsplit:  exists l1 l2, l = l1++a::l2). apply in_split. apply Hfin.
    destruct Hsplit as [l1 [l2 Hsplit]].
    unfold card.
    rewrite -> Hsplit. rewrite -> filter_app. rewrite -> filter_app.
    destruct Hne as [Hnef Hnet].
    simpl. rewrite Hnet, Hnef. rewrite app_length; rewrite app_length.
    simpl. assert (Ht : forall a b : nat, plus a (S b) = plus (plus a b) 1).
    { intros. omega. } rewrite Ht. clear Ht.
    rewrite <- app_length; rewrite <- filter_app; rewrite <- app_length; rewrite <- filter_app.
    assert (Hgt: forall a b : nat, a >= b -> plus a 1 >= plus b 1).
    { intros. omega. }  apply Hgt. clear Hgt.
    specialize (increasing O Hmon n); intros H; unfold pred_subset in H.
    induction (l1 ++ l2). auto. simpl.
    destruct (iter O n nil_pred a0) eqn: Ht.
    specialize (H a0 Ht). rewrite H.  simpl. omega.
    destruct (iter O (n + 1) nil_pred a0); simpl; omega.
  Qed.

  (*
  Inductive NoDup {A : Type} : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).
   *)

  Theorem noduplicate : forall (A : Type) (l1 l2 : list A), NoDup l1 -> NoDup l2 ->
                                                       (forall a : A, In a l1) -> length l2 <= length l1.
  Proof.
    intros A l1 l2 H1 H2 H3.
    apply NoDup_incl_length. assumption.
    unfold incl. intros. specialize (H3 a).
    assumption.
  Qed.


  Theorem operator_ext : forall {A : Type} (O : (A -> bool) -> (A -> bool)) (P Q : A -> bool) ,
      mon O -> (forall a, (P a = true <-> Q a = true))  -> (forall a, (O P a = true <->  O Q a = true)). 
  Proof.
    intros A O P Q Hmon H.
    assert (H1 : forall a, O P a = true -> O Q a = true).
    unfold mon in Hmon; unfold pred_subset in Hmon.
    apply Hmon. intros a Hp. specialize (H a). apply H. assumption.
    assert (H2 : forall a, O Q a = true -> O P a = true).
    unfold mon in Hmon; unfold pred_subset in Hmon. apply Hmon. intros a Hq.
    specialize (H a). apply H. assumption.
    intros a. split. specialize (H1 a). assumption.
    specialize (H2 a). assumption.
  Qed.
  
  Theorem  iter_aux_new {A: Type} (O: (A -> bool) -> (A -> bool)) (l: list A):
    mon O ->
    (forall a: A, In a l) ->
    forall (n : nat), (forall a:A, iter O n nil_pred a = true <-> iter O (n+1) nil_pred a = true) \/
               card l (iter O n nil_pred) >= n.
  Proof.
    intros Hmon Hfin n.  induction n.
    right. omega. destruct IHn as [Hfix | Hnfix].
    left. simpl. apply operator_ext. assumption. assumption.
    assert ((forall a : A, iter O n nil_pred a = true <-> iter O (n + 1) nil_pred a = true)
            \/ card l (iter O (n + 1) nil_pred) >= card l (iter O n nil_pred) + 1).
    apply (iter_aux O l Hmon Hfin n).
    destruct H as [Hl | Hr]. left.  simpl. apply operator_ext.
    assumption. assumption. right.
    replace (S n) with (plus n 1). omega. omega.
  Qed.
    

  Theorem  iter_aux_newagain {A: Type} (O: (A -> bool) -> (A -> bool)) (l: list A):
    mon O ->
    (forall a: A, In a l) ->
    forall (n : nat), (forall a:A, iter O n nil_pred a = true <-> iter O (n+1) nil_pred a = true) \/
               card l (iter O (n+1) nil_pred) >= (n+1).
  Proof.
    intros Hmon Hfin n.  induction n.
    destruct (iter_aux O l Hmon Hfin 0).
    left; assumption.
    right; omega.   
    destruct IHn as [Hfix | Hnfix].
    left. simpl. apply operator_ext. assumption. assumption.
    assert ((forall a : A, iter O (n + 1) nil_pred a = true <-> iter O (n + 1 + 1) nil_pred a = true)
            \/ card l (iter O (n + 1 + 1) nil_pred) >= card l (iter O (n + 1) nil_pred) + 1).
    apply (iter_aux O l Hmon Hfin (n + 1)).
    destruct H as [Hl | Hr]. left. replace (S n) with (plus n 1). assumption. omega.
    right.  replace (S n) with (plus n 1). omega. omega.
  Qed.
    

  Theorem fixedpoint_reached : forall (A : Type) (O : (A -> bool) -> (A -> bool)) (k : nat),
      mon O -> (forall a: A, iter O k nil_pred a = true <->  iter O (k + 1) nil_pred a = true) ->
      forall m, (forall a: A, iter O k nil_pred a = true <->  iter O (k + m) nil_pred a = true).
  Proof.
    intros A O k Hmon Hiter m.
    induction m. split; intros. replace (plus k 0) with k.
    assumption. omega.
    replace (plus k 0) with k in H. assumption. omega.
    specialize (operator_ext O (iter O k nil_pred) (iter O (plus k m) nil_pred) Hmon IHm).
    intros H a. split; intros.

    destruct (Hiter a) as [Hiter1 Hiter2].
    destruct (IHm a) as [IHm1 IHm2].
    destruct (H a) as [H1 H2].
    replace ((k + S m)%nat) with (S (k + m)%nat).
    simpl. apply H1. replace (plus k 1) with (S k) in Hiter1.
    simpl in Hiter1. apply Hiter1; assumption. omega. omega.

    destruct (Hiter a) as [Hiter1 Hiter2].
    destruct (IHm a) as [IHm1 IHm2].
    destruct (H a) as [H1 H2].
    apply Hiter2. replace (plus k 1) with (S k). simpl.
    apply H2. replace (plus k (S m)) with (S (plus k m)) in H0.
    simpl in H0. assumption. omega. omega.
  Qed.
  
  Theorem length_filter : forall (A : Type) (f : A -> bool) (l : list A),
      length (filter f l) <= length l.
  Proof.
    intros A f l. induction l. simpl. omega.
    simpl. destruct (f a). simpl; omega.
    omega.
  Qed.
  
  Theorem iter_fin {A: Type} (k: nat) (O: (A -> bool) -> (A -> bool)) :
    mon O -> bounded_card A k ->
    forall n: nat, forall a: A, iter O n nil_pred a = true -> iter O k nil_pred a = true.
  Proof.
    (*
    intros Hmon Hboun; unfold bounded_card in Hboun.
    destruct Hboun as [l [Hin Hlen]]. intros n a H.
    destruct (iter_aux_newagain O l Hmon Hin k) as [Hl | Hr]; swap 1 2.

    (*   Hr : card l (iter O (k + 1) nil_pred) >= k + 1 *)
    unfold card in Hr. specialize (length_filter A (iter O (plus k 1) nil_pred) l).
    intros Hl. omega.

    (*   Hl : forall a : A, iter O k nil_pred a = true <-> iter O (k + 1) nil_pred a = true *)

    
    assert (Hle : k < n \/ k >= n) by omega.    
    destruct Hle as [Hlel | Hler]; swap 1 2.
    (* k >= n *)
    clear Hlen; clear Hl.
    specialize (increasing O Hmon); intros Hinc; unfold pred_subset in Hinc.
    induction Hler. auto. specialize (Hinc m). replace (S m) with (plus m 1).
    apply Hinc. auto. omega.

    (* k < n *)
    specialize (increasing O Hmon); intros Hinc; unfold pred_subset in Hinc
    induction Hlel.
    (* base case *)
    destruct (Hl a) as [Hlf Hlb]. replace (plus k 1) with (S k) in Hlb.
    apply Hlb in H. assumption. omega.
    (* not base *)
    *)
    
    
    intros Hmon Hboun; unfold bounded_card in Hboun.
    destruct Hboun as [l [Hin Hlen]]. intros n.
    assert (Hle : k < n \/ k >= n) by omega.    
    destruct Hle as [Hlel | Hler].

    destruct (iter_aux_newagain O l Hmon Hin k).
    assert (Ht : forall a : A, iter O k nil_pred a = true <-> iter O (k + (n - k)) nil_pred a = true).
    apply fixedpoint_reached. assumption. assumption.
    replace (plus k (n - k)) with n in Ht.
    intros a H1. destruct (Ht a) as [Ht1 Ht2].
    apply Ht2. assumption. omega.

    unfold card in H. specialize (length_filter A (iter O (plus k 1) nil_pred) l).
    intros Hl. intros. omega.

    clear Hlen.
    specialize (increasing O Hmon); intros Hinc; unfold pred_subset in Hinc.
    induction Hler. auto. specialize (Hinc m). replace (S m) with (plus m 1).
    intros. apply Hinc. auto. omega.
  Qed.

  Definition pred_eq {A : Type} (p q : A -> bool) :=
    pred_subset p q /\ pred_subset q p.

  Lemma equal : forall (A : Type) (l : list A) (p q : A -> bool) (H : forall a : A, In a l),
      {pred_eq p q} + { ~(pred_eq p q)}.
  Proof.
    intros A l p q H.
    specialize (pred_eq_dec l H p q).
    intros Hdec. destruct Hdec as [Hdecl | Hdecr].
    left. unfold pred_eq; unfold pred_subset. split.
    intros a Hp. specialize (Hdecl a). rewrite Hp in Hdecl. intuition.
    intros a Hq. specialize (Hdecl a). rewrite Hq in Hdecl. intuition.
    (* case not *)
    right. unfold pred_eq. unfold pred_subset. unfold not.
    intros Hab. destruct Hab as [Hl Hr].
    apply Hdecr. intros a.
    destruct (p a) eqn: Hp. destruct (q a) eqn: Hq. auto.
    specialize (Hl a); specialize (Hr a). specialize (Hl Hp). rewrite Hl in Hq. inversion Hq.
    destruct (q a) eqn: Hq.
    specialize (Hl a); specialize (Hr a). specialize (Hr Hq). rewrite Hr in Hp. inversion Hp.
    auto.
  Qed.    


End Fixpoints.    

