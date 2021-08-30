Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Embed.Theory.Type.Affine.
Require Import Embed.Theory.Type.Positive.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Class Sing (A : Type) := {
  sing_positive :> Positive A;
  sing_affine   :> Affine A
}.

Equations is_sing {A : Type} `{singA : Sing A} (x : A) : x = positive :=
is_sing x := affine x positive.

Global Program Instance unit_Sing : Sing unit := {}.

