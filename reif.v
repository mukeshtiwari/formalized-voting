  Require Import Coq.Lists.List.


  (* type level existential quantifier *)
  Notation "'existsT' x .. y , p" :=
    (sigT (fun x => .. (sigT (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(* the following shows that a decidable (or boolean valued) predicate on a finite list
   can always be reified in terms of strong existence *)
Theorem reify {A: Type} (l: list A) (P: A -> bool) : 
  (exists x, In x l /\ P x = true) -> existsT x, P x = true.
Proof.
  intro H.
  induction l.
  contradict H.
  intro H0.
  destruct H0 as [x Hx].
  destruct Hx as [H1 H2].
  inversion H1.
  (* list not nil *)
  assert (Hbiv: {P a  = true} + {P a <> true}).
  decide equality.
  destruct Hbiv as [Htrue | Hfalse].
  exists a.
  assumption.
  (* the element is in the tail *)
  apply IHl.
  destruct H as [x Hx].
  destruct Hx as [Hl Hr].
  assert (Hin: a = x \/ In x l). apply in_inv. assumption.
  destruct Hin as [Hin1 | Hin2].
  (* case a = x: impossible *)
  subst.
  contradict Hr. assumption.
  exists x. split. assumption. assumption.
Qed.

Program Fixpoint addlist (ls1 ls2 : list nat) : list nat :=
  match ls1, ls2 with
  | n1 :: ls1',n2 :: ls2' => n1 + n2 :: addlist ls1' ls2'
  |_, _ => nil
  end.

Eval compute in fun ls => addlist nil ls.
Eval compute in fun ls => addlist ls nil.


Definition one_plus_one : 1 + 1 = 2 := eq_refl.

Definition zero_plus_n n : 0 + n = n := eq_refl.
Compute (zero_plus_n 10).
Eval compute in (zero_plus_n 10).

Fail Definition n_plus_zero n : n + 0 = n := eq_refl.

Program Definition n_plus_zero n : n + 0 = n.
induction n.
+ auto.
+ simpl. rewrite IHn. apply eq_refl.
Defined.

Print n_plus_zero.


  
Inductive expr :=
| Var : nat -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.

Example expr_ex :=
  Mul (Var 0) (Add (Var 0) (Var 1)).

Inductive isEven : nat -> Prop :=
| Even_O : isEven 0
| Even_SS n : isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
Proof.
  prove_even.
Qed.

Print even_256.

