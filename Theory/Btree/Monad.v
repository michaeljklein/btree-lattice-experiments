Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Definition ret_btree {A} : A -> @btree A := bnil.

Equations join_btree {A} (xss : @btree (@btree A)) : @btree A :=
join_btree (bnil xs) := xs ;
join_btree (bcons xs ys) := bcons (join_btree xs) (join_btree ys).

Program Instance btree_monad : @Monad Coq btree_Functor := {
  ret := fun _ => ret_btree;
  join := fun _ => join_btree
}.

Next Obligation.
revert x0.
fix join_fmap_join_btree 1.
destruct x0.
{
  rewrite fmap_btree_equation_1.
  repeat (rewrite join_btree_equation_1).
  reflexivity.
}
{
  rewrite fmap_btree_equation_2.
  repeat (rewrite join_btree_equation_2).
  refine (bcons_eq _ _).
  {
    exact (join_fmap_join_btree _).
  }
  {
    exact (join_fmap_join_btree _).
  }
}
Qed.

Next Obligation.
revert x0.
fix join_fmap_ret_btree 1.
destruct x0.
{
  rewrite fmap_btree_equation_1.
  rewrite join_btree_equation_1.
  auto.
}
{
  rewrite fmap_btree_equation_2.
  rewrite join_btree_equation_2.
  refine (bcons_eq _ _).
  {
    exact (join_fmap_ret_btree _).
  }
  {
    exact (join_fmap_ret_btree _).
  }
}
Qed.

Next Obligation.
revert x0.
fix join_fmap_fmap_btree 1.
destruct x0.
{
  rewrite fmap_btree_equation_1.
  do 2 (rewrite join_btree_equation_1).
  reflexivity.
}
{
  rewrite fmap_btree_equation_2.
  repeat (rewrite join_btree_equation_2).
  refine (bcons_eq _ _).
  {
    exact (join_fmap_fmap_btree _).
  }
  {
    exact (join_fmap_fmap_btree _).
  }
}
Qed.

