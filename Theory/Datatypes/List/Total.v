Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations total : list nat -> nat :=
total nil := 0%nat;
total (cons x xs) := x + total xs.

Fixpoint total_app (xs ys : list nat) :
  total (xs ++ ys) = (total xs + total ys)%nat.
destruct xs.
{
  reflexivity.
}
{
  rewrite total_equation_2.
  simpl.
  rewrite total_equation_2.
  rewrite <- PeanoNat.Nat.add_assoc.
  f_equal.
  exact (total_app _ _).
}
Qed.

