Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Class Positive (A : Type) := {
  positive : A
}.

Global Program Instance unit_Positive : Positive unit := {
  positive := tt
}.

Global Program Instance bool_Positive : Positive bool := {
  positive := false
}.

