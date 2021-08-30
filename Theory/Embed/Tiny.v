Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

Require Import Category.Lib.
Require Import Category.Instance.Fun.
Require Import Category.Theory.

From Equations Require Import Equations.
Require Import Equations.Type.Loader.
Unset Equations With Funext.
Set Equations Transparent.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Class Funext := {
  funext {A : Type} {B : A -> Type} :
    forall (f g : forall x, B x), (forall x, f x = g x) -> f = g
}.

Definition Embed (A : Type) : Type :=
  A -> Type.

Definition MapEmbed {A : Type} (P Q : Embed A) :=
  ∀ x, P x -> Q x.

Notation "P ⥤ Q" := (MapEmbed P Q)
  (at level 90, right associativity) : category_scope.

Program Instance MapEmbedC (A : Type) : Category := {
  obj     := Embed A;
  hom     := MapEmbed;
  homset  := λ _ _, {| equiv := λ fs gs, ∀ x xs, fs x xs = gs x xs |};
  id      := λ _ _ x, x;
  compose := λ _ _ _ P Q x xs, P x (Q x xs)
}.
Next Obligation. apply Build_Equivalence; congruence. Qed.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.

Definition U1 {A : Type} : Embed A :=
  λ _, Datatypes.unit.

Program Instance MapEmbedC_Terminal : @Terminal (MapEmbedC A) := { terminal_obj := U1 }.
Next Obligation. unfold U1. tauto. Qed.
Next Obligation. destruct (f x0 xs), (g x0 xs); reflexivity. Qed.

Program Instance EmbedC : Category := {
  obj     := Type;
  hom     := λ A B, [MapEmbedC A, MapEmbedC B];
  id      := λ _, Functor.Id;
  compose := λ _ _ _, Compose
}.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.

Definition NP {A : Type} (P : Embed A) :
  Embed {x & P x} -> Embed A :=
  λ f x, ∀ i, f (existT _ x i).

Program Definition NP_Functor `{Funext} {A : Type} (P : Embed A) :
  {x & P x} ~{EmbedC}~> A :=
  {| fmap {f g} fg x xs i := fg (existT P x i) (xs i)
 |}.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.

Definition NS {A : Type} (P : Embed A) : Embed {x & P x} -> Embed A :=
  λ f x, {i & f (existT _ x i) }.

Program Definition NS_Functor {A : Type} (P : Embed A) :
  {x & P x} ~{EmbedC}~> A :=
  {| fmap {f g} := λ fg x xs, (`1 (xs); fg `1 (xs) `2 (xs)) |}.
Next Obligation. proper; induction xs; congruence. Qed.
Next Obligation. proper; induction xs; reflexivity. Qed.
Next Obligation. proper. Qed.

