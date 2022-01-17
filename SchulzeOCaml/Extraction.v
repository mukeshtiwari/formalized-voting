Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import SchulzeSynthesis.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.
Require Extraction.

Extraction Language OCaml.
Extraction "lib.ml" schulze_winners_pf.
