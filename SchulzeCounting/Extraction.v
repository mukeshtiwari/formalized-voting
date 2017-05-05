Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import SchulzeSynthesis.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.

Extraction Language Ocaml.
Extraction "Lib.ml" schulze_winners_pf.
