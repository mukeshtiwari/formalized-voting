Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Require Import ListLemma.
Import ListNotations.
Open Scope Z.

Section Evote.
  (** Section 2: Specification of Schulze Vote Counting **)

  (* candidates are a finite type with decidable equality *)
  Parameter cand : Type.
  Parameter cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.

  (* marg is the margin in Schulze counting, i.e. marg c d is the number of 
   voters that perfer c over d. The existence of the margin function
   is assumed for the specification of Schulze Voting and will be
   constructed from incoming ballots later *)
  Variable marg : cand -> cand -> Z. 
  
  (* prop-level path *)
  Inductive Path (k: Z) : cand -> cand -> Prop :=
  | unit c d : marg c d >= k -> Path k c d
  | cons  c d e : marg c d >= k -> Path k d e -> Path k c e.
  
  (* winning condition of Schulze Voting *)
  Definition wins_prop (c: cand) :=
    forall d : cand, exists k : Z, 
        ((Path k c d) /\ (forall l, Path l d c -> l <= k)).
  
  (* dually, the notion of not winning: *)
  Definition loses_prop (c : cand) :=
    exists k d, Path k d c /\ (forall l, Path l c d -> l < k).
 
  (** Section 3 **)
  
  (* boolean function that determines whether the margin between a
     pair  of candidates is below a given integer *)
  Definition marg_lt (k : Z) (p : (cand * cand)) :=
    Zlt_bool (marg (fst p) (snd p)) k.
  
  (* definition of the (monotone) operator W_k that defines coclosed sets *)
  Definition W (k : Z) (p : cand * cand -> bool) (x : cand * cand) :=
    andb 
      (marg_lt k x) 
      (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all).

  (* k-coclosed predicates *)
  Definition coclosed (k : Z) (p : (cand * cand) -> bool) :=
    forall x, p x = true -> W k p x = true.

  (* type-level path to replace prop-level path *)
  Inductive PathT (k: Z) : cand -> cand -> Type :=
  | unitT : forall c d, marg c d >= k -> PathT k c d
  | consT : forall c d e, marg c d >= k -> PathT k d e -> PathT k c e.
  
  (* type-level winning condition in Schulze counting *)
  Definition wins_type c :=
    forall d : cand, existsT (k : Z),
    ((PathT k c d) *
     (existsT (f : (cand * cand) -> bool), f (d, c) = true /\ coclosed (k + 1) f))%type.

  (* dually, the type-level condition for non-winners *)
  Definition loses_type (c : cand) :=
    existsT (k : Z) (d : cand),
    ((PathT k d c) *
     (existsT (f : (cand * cand) -> bool), f (c, d) = true /\ coclosed k f))%type.

  (* type-level notions of winning and losing are equivalent *)
  (* auxilary lemmas needed for the proof of equivalence     *)
  (* search for wins_prop_type and wins_type_prop for the    *)
  (* statement and proof of equivalence, dually for losing.  *)

  (**** all lemmas needed for the proof of the below should go here ****)

   (* type-level paths allow to construct evidence for the existence of paths *)
  Lemma path_equivalence : forall c d k , PathT k c d -> Path k c d.
  Proof.
    intros c d k H.
    induction H; [constructor 1 | constructor 2 with d]; auto.
  Qed.

  Lemma mp_log : forall (k : Z) (x : cand * cand) (p : cand * cand -> bool),
      (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all) = true ->
      forall b, p (b, snd x) = true \/ marg (fst x) b < k.
   Proof.
     intros k x p H b.
     assert (Hin : In b cand_all) by  apply cand_fin.
     pose proof (proj1 (forallb_forall _ cand_all) H b Hin) as Hp. simpl in Hp.
     apply orb_true_iff in Hp; destruct Hp as [Hpl | Hpr]; destruct x as (a, c); simpl in *.
     + right; apply Zlt_is_lt_bool; auto.
     + left;auto.
   Qed.

   Lemma coclosed_path : forall k f, coclosed k f -> forall s x y,
        Path s x y -> f (x, y) = true -> s < k.
  Proof.
    intros k f Hcc x s y p. induction p.
    (* unit path *)
    + intros Hin; specialize (Hcc (c, d) Hin); apply andb_true_iff in Hcc;
        destruct Hcc as [Hccl Hccr]; apply Zlt_is_lt_bool in Hccl; simpl in Hccl;  omega.
    (* non unit path *)
    + intros Hin; specialize (Hcc (c, e) Hin); apply andb_true_iff in Hcc;
        destruct Hcc as [Hccl Hccr]; unfold marg_lt in Hccl; simpl in Hccl.
      assert (Hmp : forall m, f (m, (snd (c, e))) = true \/ marg (fst (c, e)) m < k)
        by (apply mp_log; auto); simpl in Hmp.
      specialize (Hmp d). destruct Hmp; [intuition | omega].
  Qed.
  
  (**** all generic lemmas about lists etc. should go elsewhere ****)

  (* the type level winning condition can be reconstruced from *)
  (* propositional knowledge of winning *)
  Lemma wins_prop_type : forall c, wins_prop c -> wins_type c.
  Proof.
    intros c H. unfold wins_prop, wins_type in *.
    apply L15. apply L14. auto.
  Qed.

  (* dually, the type-level information witnessing winners *)
  (* entails prop-level knowledge. *)
  Lemma wins_type_prop : forall c, wins_type c -> wins_prop c.
  Proof.
    intros c H. unfold wins_prop, wins_type in *. intros d.
    destruct (H d) as [k [H1 [f [H3 H4]]]].
    exists k. split. apply path_equivalence. auto.
    intros l H5. pose proof (coclosed_path _ _ H4).
    pose proof (H0 l _ _ H5 H3). omega.
  Qed.
