Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import fp_finite_Dirk.
Require Import Schulze_Dirk.
Import ListNotations.

Module Voting.

  Parameter cand : Type.
  Parameter ballot : list cand.
  Hypothesis cand_fin : forall c: cand, In c ballot.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  
  Fixpoint cross_prod (l : list cand) : list (cand * cand) :=
    match l with
    | [] => []
    | h :: t => map (fun x => (h, x)) t ++ cross_prod t
    end.

 
  Fixpoint valid_ballot (l : list cand) : Prop :=
    match l with
    | [] => True
    | h :: t => (In h ballot) /\ valid_ballot t
    end.

  Definition cand_eqb (c d: cand) := proj1_sig (bool_of_sumbool (dec_cand c d)).

  Definition bool_in (p: cand) (l: list cand) :=
    existsb (fun q => cand_eqb p q) l. 
  
  Fixpoint valid_ballot_bool (l : list cand) : bool :=
    match l with
    | [] => true
    | h :: t => andb (list_member h ballot) (valid_ballot_bool t)
    end.
  
  Inductive valid_ballot_ind : list cand -> Prop :=
  | Empty_valid : valid_ballot_ind nil
  | Cons_valid h t : In h ballot -> valid_ballot_ind t -> valid_ballot_ind (h :: t).

 
  Fixpoint margin_fun (c1 c2 : cand) (l : list (list cand)) : nat :=
    let l := concat (map (fun x => cross_prod x) l) in
    let m := filter (fun t => andb (cand_eqb (fst t) c1) (cand_eqb (snd t) c2)) l in
    length m.

  
    
  
End Voting.

