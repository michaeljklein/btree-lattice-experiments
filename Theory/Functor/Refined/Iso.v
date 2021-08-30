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

Section IsoRefined.
Context `{F : Coq ⟶ Coq}.

Definition iso_refined (x y : F 1) : Type :=
  forall A, refined x A ≅ refined y A.

Global Program Instance equiv_iso_refined : Equivalence iso_refined.
Next Obligation.
proper.
Qed.
Next Obligation.
proper.
exact (iso_sym (X A)).
Qed.
Next Obligation.
proper.
exact (iso_compose (X0 A) (X A)).
Qed.

Equations id_iso_refined (x : F 1) : iso_refined x x :=
id_iso_refined _ _ := iso_id.

Equations compose_iso_refined {x y z : F 1}
  (yz : iso_refined y z)
  (xy : iso_refined x y) :
    iso_refined x z :=
compose_iso_refined yz xy w := iso_compose (yz w) (xy w).

Definition iso_refined_equiv {x y : F 1} : crelation (iso_refined x y) :=
  fun xs ys => forall A, isomorphism_equiv (xs A) (ys A).

Global Program Instance equiv_iso_refined_equiv {x y} : Equivalence (@iso_refined_equiv x y).
Next Obligation.
proper.
Qed.
Next Obligation.
proper.
Qed.
Next Obligation.
proper.
exact (@Equivalence_Transitive _ isomorphism_equiv _ _ _ _ (X A) (X0 A)).
Qed.

Program Instance RefinedCat : Category := {
  obj     := F 1;
  hom     := iso_refined;
  homset  := fun _ _ => {|
      equiv        := iso_refined_equiv;
      setoid_equiv := equiv_iso_refined_equiv
    |};
  id      := id_iso_refined;
  compose := fun _ _ _ => compose_iso_refined
}.
Next Obligation.
proper.
repeat (rewrite compose_iso_refined_equation_1).
pose (X' := X A).
pose (X0' := X0 A).
destruct X', X0'.
split.

intro.
simpl.
rewrite (e1 x2).
rewrite (e _).
reflexivity.

intro.
simpl.
rewrite (e0 x2).
rewrite (e2 _).
reflexivity.
Qed.

Next Obligation.
intro.
rewrite compose_iso_refined_equation_1.
rewrite id_iso_refined_equation_1.
split.

intro.
auto.

intro.
auto.
Qed.

(* Same as last proof *)
Next Obligation.
intro.
rewrite compose_iso_refined_equation_1.
rewrite id_iso_refined_equation_1.
split.

intro.
auto.

intro.
auto.
Qed.

Next Obligation.
intro.
repeat (rewrite compose_iso_refined_equation_1).
split.

intro.
auto.

intro.
auto.
Qed.

(* Same as last proof *)
Next Obligation.
intro.
repeat (rewrite compose_iso_refined_equation_1).
split.

intro.
auto.

intro.
auto.
Qed.

End IsoRefined.

