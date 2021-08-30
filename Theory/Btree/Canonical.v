Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Leaves.

Generalizable All Variables.
Set Universe Polymorphism.

Equations canonical_btree (n : nat) : @btree 1 :=
canonical_btree O := bnil tt;
canonical_btree (S n) := bcons (bnil tt) (canonical_btree n).

Fixpoint num_leaves_canonical_btree (n : nat) :
  num_leaves (canonical_btree n) = S n.
destruct n.

reflexivity.

rewrite canonical_btree_equation_2.
rewrite num_leaves_equation_2.
rewrite num_leaves_equation_1.
refine (eq_S _ _ _).
exact (num_leaves_canonical_btree n).
Qed.

