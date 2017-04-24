Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import SchulzeSynthesis.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.

Extraction Language Haskell.
Extraction "Lib.hs" schulze_winners_pf.
