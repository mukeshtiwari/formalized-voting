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
Import ListNotations.
Open Scope Z.
Section Evote. 

  (* type level existential quantifier *)
  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'") : type_scope.

  Parameter cand : Type.
  Parameter cand_all : list cand.
  Hypothesis cand_fin : forall c: cand, In c cand_all.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_not_nil : cand_all <> nil.
