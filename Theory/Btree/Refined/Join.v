Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Datatypes.Prod.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.

Require Import Embed.Theory.Btree.Refined.Iso.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations piso_refined_btree_bnil_to (x : @btree 1) (A : Type) :
  @refined (Compose btree_Functor btree_Functor) (bnil x) A -> refined x A :=
piso_refined_btree_bnil_to _ _ (@exist _ _ (bnil xs) _) := @exist _ _ xs _;
piso_refined_btree_bnil_to _ _ (@exist _ _ (bcons _ _) _) := _.

Equations piso_refined_btree_bnil_from (x : @btree 1) (A : Type) :
  refined x A -> @refined (Compose btree_Functor btree_Functor) (bnil x) A :=
piso_refined_btree_bnil_from _ _ (@exist _ _ xs _) := @exist _ _ (bnil xs) _.

Program Instance piso_refined_btree_bnil (x : @btree 1) (A : Type) :
    @refined (Compose btree_Functor btree_Functor) (bnil x) A ≅ refined x A := {
      to   := piso_refined_btree_bnil_to _ _;
      from := piso_refined_btree_bnil_from _ _
}.
Next Obligation.
destruct x0.
rewrite piso_refined_btree_bnil_from_equation_1.
rewrite piso_refined_btree_bnil_to_equation_1.
simpl.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec dec_eq_btree _ _).
Qed.

Next Obligation.

destruct x0.
destruct x.

destruct x0.

destruct f.

destruct u.
simpl in e.
simpl.
rewrite piso_refined_btree_bnil_to_equation_1.
rewrite piso_refined_btree_bnil_from_equation_1.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec (@dec_eq_btree _ dec_eq_btree) _ e).

discriminate.

discriminate.

destruct x0.
2: {
  discriminate.
}

destruct f.

discriminate.

rewrite piso_refined_btree_bnil_to_equation_1.
rewrite piso_refined_btree_bnil_from_equation_1.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec (@dec_eq_btree _ dec_eq_btree) _ e).
Qed.

Equations piso_refined_btree_bcons_to {x y : @btree (@btree 1)} {A : Type} :
  @refined (Compose btree_Functor btree_Functor) (bcons x y) A ->
  @refined (Compose btree_Functor btree_Functor) x A * @refined (Compose btree_Functor btree_Functor) y A :=
piso_refined_btree_bcons_to (@exist _ _ (bnil _) _) := _;
piso_refined_btree_bcons_to (@exist _ _ (bcons xs ys) _) := pair (@exist _ _ xs _) (@exist _ _ ys _).

Equations piso_refined_btree_bcons_from {x y : @btree (@btree 1)} {A : Type} :
  @refined (Compose btree_Functor btree_Functor) x A * @refined (Compose btree_Functor btree_Functor) y A ->
  @refined (Compose btree_Functor btree_Functor) (bcons x y) A :=
piso_refined_btree_bcons_from (pair (@exist _ _ xs _) (@exist _ _ ys _)) :=
  @exist _ _ (bcons xs ys) _.

Program Instance piso_refined_btree_bcons (x y : @btree (@btree 1)) (A : Type) :
  @refined (Compose btree_Functor btree_Functor) (bcons x y) A ≅
  @refined (Compose btree_Functor btree_Functor) x A * @refined (Compose btree_Functor btree_Functor) y A := {
    to   := piso_refined_btree_bcons_to;
    from := piso_refined_btree_bcons_from
}.
Next Obligation.
destruct r, r0.
rewrite piso_refined_btree_bcons_from_equation_1.
rewrite piso_refined_btree_bcons_to_equation_2.
refine (pair_eq _ _).

refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec (@dec_eq_btree _ dec_eq_btree) _ e).

refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec (@dec_eq_btree _ dec_eq_btree) _ e0).
Qed.

Next Obligation.
destruct x0.
destruct x0.

discriminate.

rewrite piso_refined_btree_bcons_to_equation_2.
rewrite piso_refined_btree_bcons_from_equation_1.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
simpl.
exact (UIP_dec (@dec_eq_btree _ dec_eq_btree) _ e).
Qed.

Fixpoint piso_refined_btree (x : @btree (@btree 1)) : forall {A : Type},
  @refined (Compose btree_Functor btree_Functor) x A ≅
    refined (join_btree x) A.
intro.
destruct x.

rewrite join_btree_equation_1.
exact (piso_refined_btree_bnil _ _).

rewrite join_btree_equation_2.

refine (iso_compose _ (piso_refined_btree_bcons x1 x2 A)).
refine (iso_compose (iso_sym (refined_bcons (join_btree x1) (join_btree x2) A)) _).
Defined.

