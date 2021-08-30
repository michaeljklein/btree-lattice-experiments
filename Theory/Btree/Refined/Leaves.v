Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Functor.Refined.Iso.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Leaves.

Require Import Embed.Theory.Btree.Canonical.
Require Import Embed.Theory.Btree.Canonical.Refined.
Require Import Embed.Theory.Btree.Canonical.Refined.Iso.

Require Import Embed.Theory.Utils.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Lemma iso_refined_btree_eq_num_leaves (x y : @btree 1) :
  iso_refined x y -> num_leaves x = num_leaves y.
intro.

pose (H := iso_refined_canonical_btree_eq _ _ (compose_iso_refined
  (compose_iso_refined
    (iso_refined_canonical_btree y)
    X
  )
  (@Equivalence_Symmetric _ iso_refined _ _ _ (iso_refined_canonical_btree x))
)).
repeat (rewrite <- PeanoNat.Nat.sub_1_r in H).
refine (refine_nat_pred_positive _ _ H).

exact (num_leaves_positive _).

exact (num_leaves_positive _).
Qed.

(* Much easier than the other direction: we just use iso_refined_canonical_btree *)
Lemma eq_num_leaves_iso_refined_btree (x y : @btree 1) :
  num_leaves x = num_leaves y -> iso_refined x y.
proper.
pose (Hx := @iso_refined_canonical_btree x A).
pose (Hy := @iso_refined_canonical_btree y A).
rewrite <- H in Hy.
exact (iso_compose (iso_sym Hy) Hx).
Qed.

Theorem iso_refined_num_leaves (x y : @btree 1) :
  iso_refined x y ↔ num_leaves x = num_leaves y.
split.

exact (iso_refined_btree_eq_num_leaves x y).

exact (eq_num_leaves_iso_refined_btree x y).
Defined.

Corollary not_iso_refined_bcons_bnil (x y : @btree 1)
  (pf : @iso_refined btree_Functor (bcons x y) (bnil tt)) : False.
pose (H := iso_refined_btree_eq_num_leaves (bcons x y) (bnil tt) pf).
simpl in H.
destruct (Plus.plus_is_one _ _ H).

destruct a.
destruct (num_leaves_positive x H0).

destruct a.
destruct (num_leaves_positive y H1).
Qed.

