Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import SchulzeSynthesis.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.

Extraction Language Haskell.

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive Datatypes.nat => "Prelude.Int" ["0"
  "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inlined Constant Nat.ltb   => "(Prelude.<)".


Extraction "LibNative.hs" schulze_winners_pf.

