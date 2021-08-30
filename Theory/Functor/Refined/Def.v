Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section FunctorRefinedDef.
Context `{F : Coq ⟶ Coq}.
Context (x : F 1).

Definition refined (A : Type) :=
  { y : F A | void y = x }.

Definition fmap_refined {A B} (f : A -> B) (xss : refined A) : refined B.
destruct xss.
refine (exist _ (fmap f x0) _).
replace (@void Coq _ F _ (@fmap Coq Coq F A B f x0)) with ((void ∘ fmap f) x0) by reflexivity.
rewrite (@void_fmap Coq _ F _ _ f).
exact e.
Defined.

End FunctorRefinedDef.

Section FunctorRefined.
Context `{F : Coq ⟶ Coq}.
Context `(x : F 1).
Context `{F1_dec : EqDec (F 1)}.

(* Requires F1_dec *)
Lemma eq_refined {A} (xs ys : refined x A) (pf : proj1_sig xs = proj1_sig ys) : xs = ys.
destruct xs, ys.
unfold proj1_sig in pf.

refine (eq_sig (exist (λ y : F A, void y = x) x0 e) (exist (λ y : F A, void y = x) x1 e0) pf _).
simpl.
refine (UIP_dec F1_dec _ _).
Defined.

Lemma refined_EqDec {A} {FA_dec : EqDec (F A)} : EqDec (refined x A).
proper.
pose (H := eq_refined x0 y).
destruct x0, y.
simpl in H.
destruct (FA_dec x0 x1).

refine (Specif.left _).
exact (H e1).

refine (Specif.right _).
intro.
congruence.
Qed.

Polymorphic Program Instance refined_Functor : Coq ⟶ Coq := {|
  fmap {f g} := fmap_refined x
|}.
Next Obligation.
proper.
destruct x2.
unfold fmap_refined.
simpl.
refine (eq_refined _ _ _).
simpl.
rewrite (@fmap_respects _ Coq F x0 y x1 y0 H x2).
reflexivity.
Defined.

Next Obligation.
unfold fmap_refined.
simpl.
destruct x1.
refine (eq_refined _ _ _).
simpl.
rewrite (@fmap_id _ _ F).
reflexivity.
Defined.

Next Obligation.
unfold fmap_refined.
destruct x1.
simpl.
refine (eq_refined _ _ _).
simpl.
replace (fmap[F] (λ x2 : x0, f (g x2)) x1) with (fmap[F] (f ∘ g) x1) by reflexivity.
rewrite (@fmap_comp _ _ F).
reflexivity.
Defined.

End FunctorRefined.

