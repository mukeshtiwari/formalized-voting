Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import schulzecomputation.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import EqNat.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].


Extract Inlined Constant andb      => "(Prelude.&&)".
Extract Inlined Constant app       => "(Prelude.++)".

Extract Inlined Constant fst       => "Prelude.fst".
Extract Inlined Constant length    => "Data.List.length".

Extract Inlined Constant minus     => "(Prelude.-)".
Extract Inlined Constant mult      => "(Prelude.*)".
Extract Inlined Constant negb      => "Prelude.not".
Extract Inlined Constant orb       => "(Prelude.||)".
Extract Inlined Constant plus      => "(Prelude.+)".
Extract Inlined Constant proj1_sig => "".
Extract Inlined Constant projT1    => "Prelude.fst".

Extract Inlined Constant snd       => "Prelude.snd".
Extraction Implicit eq_rect [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec [ x y ].
Extraction Implicit eq_rec_r [ x y ].

Extract Inlined Constant eq_rect => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec => "".
Extract Inlined Constant eq_rec_r => "".

Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].


Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive positive =>
  "Prelude.Integer" [
      "(\x -> 2 Prelude.* x Prelude.+ 1)"
        "(\x -> 2 Prelude.* x)"
        "1" ]
                    "(\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))".

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
                                        "(\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))".
Extract Constant positive_eq_dec => "(Prelude.==)".
Extraction "vote.hs" final_count. 
