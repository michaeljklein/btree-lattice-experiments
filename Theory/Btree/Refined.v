Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Functor.Refined.Iso.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.

Require Import Embed.Theory.Btree.Refined.Iso.
Require Import Embed.Theory.Btree.Refined.Leaves.
Require Import Embed.Theory.Btree.Refined.Join.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Lemma iso_refined_btree_void_ret {A} (x : @btree A)
  (pf : iso_refined (void[btree_Functor] x) (bnil ())) :
    { y | ret y = x}.
destruct x.
exact (exist _ a eq_refl).
unfold void in pf.
simpl in pf.
unfold ret_btree in pf.
rewrite fmap_btree_equation_2 in pf.
pose (not_iso_refined_bcons_bnil (fmap_btree (λ _ : A, ()) x1) (fmap_btree (λ _ : A, ()) x2)).
destruct (f pf).
Qed.

Lemma iso_refined_btree_void_ret_join {A} (x : @btree (@btree A))
  (pf : iso_refined (void x) (ret tt)) :
  ret (join x) = x.
destruct x.

reflexivity.

rewrite join_btree_equation_2.
destruct (iso_refined_btree_void_ret (bcons x1 x2) pf).
simpl in e.
unfold ret_btree in e.
discriminate.
Qed.

Lemma iso_refined_btree_void_join (x : @btree (@btree 1)) (y : @btree 1)
  (pf : iso_refined (join[btree_Functor] x) y) (A : Type) :
    @refined (Compose btree_Functor btree_Functor) x A ≅ refined y A.
pose (pf A).
exact (iso_compose _ (piso_refined_btree x)).
Defined.

