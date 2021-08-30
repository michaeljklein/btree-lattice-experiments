Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Class Affine (A : Type) :=
  affine : forall (x y : A), x = y.

Global Program Instance unit_Affine : Affine Datatypes.unit := {}.

Global Program Instance False_Affine : Affine False := {}.
Next Obligation.
destruct x.
Qed.

(* iff is an isomorphism over Affine embeddings *)
Program Instance affine_iff_iso {A} (f : A -> Type) `{affineF : forall x, Affine (f x)} (x y : A)
  (affine_iff : f x ↔ f y) : f x ≅ f y := {
    to   := fst affine_iff;
    from := snd affine_iff
}.
Next Obligation.
exact (affineF _ _ _).
Qed.

Next Obligation.
exact (affineF _ _ _).
Qed.

