Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Datatypes.Prod.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations refined_bnil_to {A} (xs : refined (bnil tt) A) : A :=
refined_bnil_to (@exist (bnil y) _) := y;
refined_bnil_to (@exist (bcons _ _) _) := _.

Equations refined_bnil_from {A} (x : A) : refined (bnil tt) A :=
refined_bnil_from y := exist _ (bnil y) eq_refl.

Program Instance refined_bnil A :
  refined (bnil tt) A ≅ A := {
    to   := refined_bnil_to;
    from := refined_bnil_from
}.
Next Obligation.
destruct x.
destruct x.

rewrite refined_bnil_to_equation_1.
rewrite refined_bnil_from_equation_1.
refine (eq_sig _ _ ?[simpl_reflexivity] _).
refine (@UIP_dec (@btree 1) dec_eq_btree _ _ _ _).

[simpl_reflexivity] :{
  simpl.
  reflexivity.
}

discriminate.
Qed.

Equations refined_bcons_to {x y : @btree 1} {A} (xs : refined (bcons x y) A) :
  refined x A * refined y A :=
refined_bcons_to (@exist (bnil z) pf) := _;
refined_bcons_to (@exist (bcons z w) pf) :=
  pair
    (exist _ z _)
    (exist _ w _).

Equations refined_bcons_from {x y : @btree 1} {A} (xs : refined x A * refined y A) :
  refined (bcons x y) A := 
refined_bcons_from (pair (@exist z pfZ) (@exist w pfW)) :=
  exist _ (bcons z w) _.

Polymorphic Program Instance refined_bcons (x y : @btree 1) A :
  refined (bcons x y) A ≅ refined x A * refined y A := {
    to   := refined_bcons_to;
    from := refined_bcons_from
}.
Next Obligation.
destruct r, r0.
rewrite refined_bcons_from_equation_1.
rewrite refined_bcons_to_equation_2.
refine (pair_eq _ _).

refine (eq_sig _ _ ?[simpl_reflexivity] _).
refine (@UIP_dec (@btree 1) dec_eq_btree _ _ _ _).

[simpl_reflexivity] :{
  simpl.
  reflexivity.
}

refine (eq_sig _ _ ?[simpl_reflexivity] _).
refine (@UIP_dec (@btree 1) dec_eq_btree _ _ _ _).

[simpl_reflexivity] :{
  simpl.
  reflexivity.
}
Qed.

Next Obligation.
destruct x0.
destruct x0.

discriminate.

rewrite refined_bcons_to_equation_2.
rewrite refined_bcons_from_equation_1.

refine (eq_sig _ _ ?[simpl_reflexivity] _).
refine (@UIP_dec (@btree 1) dec_eq_btree _ _ _ _).

[simpl_reflexivity] :{
  simpl.
  reflexivity.
}
Qed.

