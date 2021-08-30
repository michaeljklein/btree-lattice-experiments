Set Warnings "-notation-overridden".

(* Require Import Coq.Program.Basics. *)
(* Require Import Coq.Lists.List. *)
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Monad.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Functor.Refined.Iso.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.

Require Import Embed.Theory.Btree.Refined.
Require Import Embed.Theory.Btree.Refined.Leaves.
Require Import Embed.Theory.Bforest.Is.
(* Require Import Embed.Theory.Btree.Zip. *)

Require Import Embed.Theory.Type.Affine.
Require Import Embed.Theory.Utils.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.


Definition is_btree_section {A : Type} (x y : @btree 1) (z : @btree (@btree A)) : Prop :=
  num_leaves (void z) = num_leaves x /\
  num_leaves (void (join z)) = num_leaves y.

Global Program Instance is_btree_section_Affine {A : Type}
  {x y : @btree 1} {z : @btree (@btree A)} : Affine (is_btree_section x y z) := {}.
Next Obligation.
destruct x0, y0.
rewrite (UIP_dec nat_EqDec e e1).
rewrite (UIP_dec nat_EqDec e0 e2).
reflexivity.
Qed.

(* All four proofs are almost the same *)
Lemma is_btree_section_iff_is_bforest {A : Type} (x y : @btree 1) (z : @btree (@btree A)) :
  is_btree_section x y z ↔ is_bforest (num_leaves x) (num_leaves y) (leaves z).
split.
{
  intro.
  destruct H.
  refine (conj _ _).
  {
    unfold void.
    rewrite <- H.
    rewrite eq_num_leaves.
    unfold void.
    rewrite num_leaves_fmap.
    reflexivity.
  }
  {
    rewrite <- H0.
    unfold void.
    rewrite <- num_leaves_join.
    rewrite num_leaves_fmap.
    reflexivity.
  }
}
{
  intro.
  destruct H.
  refine (conj _ _).
  {
    unfold void.
    rewrite num_leaves_fmap.
    rewrite H.
    rewrite eq_num_leaves.
    reflexivity.
  }
  {
    unfold void.
    rewrite num_leaves_fmap.
    rewrite H0.
    rewrite <- num_leaves_join.
    reflexivity.
  }
}
Qed.

Lemma unfold_is_btree_section {A : Type} {x y : @btree 1} {z : @btree (@btree A)} :
  is_btree_section x y z ↔
  iso_refined (void z) x *
  iso_refined (void (join z)) y.
split.
{
  intro.
  destruct H.
  refine (pair _ _).
    {
      exact (snd (iso_refined_num_leaves _ _) H).
    }
    {
      exact (snd (iso_refined_num_leaves _ _) H0).
    }
}
{
  intro.
  destruct X.
  refine (conj _ _).
    {
      exact (fst (iso_refined_num_leaves _ _) i).
    }
    {
      exact (fst (iso_refined_num_leaves _ _) i0).
    }
}
Defined.

Lemma is_btree_section_iso_refined_void_join {A : Type} {x y : @btree 1} {z : @btree (@btree A)} :
  is_btree_section x y z ->
  @refined (Compose btree_Functor btree_Functor) (fmap void z) A ≅ refined y A.
intro.
destruct (fst unfold_is_btree_section H).
pose (join_fmap_fmap one z).
simpl in e.
replace (fmap_btree (λ _ : A, ())) with
        (@void btree_Functor A) in e by reflexivity.
replace join_btree with (@join _ btree_Functor _ A) in e by reflexivity.
rewrite <- e in i0.
exact (iso_refined_btree_void_join _ _ i0 A).
Defined.



Equations is_btree_section_lower_refined {A : Type} {x y : @btree 1} {xy : @btree (@btree A)}
  (xys : is_btree_section x y xy) : refined x 1 :=
is_btree_section_lower_refined xys := @exist _ _ x (void_1 x).

Equations is_btree_section_upper_refined {A : Type} {x y : @btree 1} {xy : @btree (@btree A)}
  (xys : is_btree_section x y xy) : refined y A :=
is_btree_section_upper_refined xys :=
  to (snd (fst unfold_is_btree_section xys) A) (@exist _ _ (join xy) eq_refl).

(* - xys is a proof that yzs can be split along its "root" btree, by is_btree_section_iso_refined_void_join *)
(* - use that to split yz and then (fmap join) it *)
Equations compose_is_btree_section_helper {A B : Type} {x y z : @btree 1} {yz : @btree (@btree A)} {xy : @btree (@btree B)}
  (yzs : is_btree_section y z yz)
  (xys : is_btree_section x y xy) : @btree (@btree A) :=
compose_is_btree_section_helper yzs xys :=
  proj1_sig (
    from
      (is_btree_section_iso_refined_void_join yzs)
      (is_btree_section_upper_refined yzs)
  ).

