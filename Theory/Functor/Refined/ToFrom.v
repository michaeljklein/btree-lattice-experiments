Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section ToFromRefined.
Context `{F : Coq ⟶ Coq}.

Equations to_refined {A} (x : F A) : refined (void x) A :=
to_refined xs := exist _ xs eq_refl.

Equations from_refined {A} {x : F 1} (xs : refined x A) : F A :=
from_refined (exist _ y _) := y.
Global Transparent from_refined.

Lemma from_to_refined {A} (x : F A) :
  from_refined (to_refined x) = x.
rewrite to_refined_equation_1.
rewrite from_refined_equation_1.
reflexivity.
Qed.

Lemma void_from_refined {A} {x : F 1} (xs : refined x A) :
  void (from_refined xs) = x.
destruct xs.
rewrite from_refined_equation_1.
exact e.
Defined.

Check (forall {A} {x : F A} (xs : refined (void x) A),
  to_refined (from_refined xs) =
    eq_rect _ (fun y => refined y A)
    xs (void (from_refined xs))
    (eq_sym (void_from_refined xs))
).

Lemma to_from_refined {F1_dec : EqDec (F 1)} {A}
  {x : F A} (xs : refined (void x) A) :
    to_refined (from_refined xs) =
      eq_rect _ (fun y => refined y A)
      xs
      (void (from_refined xs))
      (eq_sym (void_from_refined xs)).
destruct xs.
rewrite to_refined_equation_1.
refine (eq_refined _ _ _ _).
simpl.
rewrite <- e.
unfold eq_rect.
unfold void_from_refined.
unfold from_refined_equation_1.
unfold eq_ind_r.
unfold eq_sym.
unfold eq_ind.
reflexivity.
Defined.

End ToFromRefined.

