Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.

(* for void *)
Require Import Embed.Theory.Functor.Void.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section FunctorDecomposeCats.

(* The image of a Functor over a Category *)
Program Instance ImageCat {C D : Category} (F : C ⟶ D) : Category := {
  obj     := obj[C];
  hom     := fun A B => F A ~> F B;
  homset  := fun _ _ => {| equiv := equiv |};
  id      := fun x => fmap[F] id[x];
}.

Program Instance FunctorCat {C : Category} (F : C ⟶ Coq) : Category := {
  obj     := { x : obj[C] & F x };
  hom     := fun xs ys => F (projT1 xs) ~> F (projT1 ys);
  homset  := fun _ _ => {| equiv := equiv |};
  id      := fun x => fmap[F] id[projT1 x];
}.
Next Obligation.
rewrite (@fmap_id _ _ F _ (f x0)).
reflexivity.
Qed.
Next Obligation.
rewrite (@fmap_id _ _ F).
reflexivity.
Qed.

End FunctorDecomposeCats.

