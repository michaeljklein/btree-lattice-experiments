Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Btree.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Definition void {f : @Functor Coq Coq} {x} : f x ~> f 1 := fmap one.

Equations fmap_btree {A B : Type} (f : A -> B) : @btree A -> @btree B :=
fmap_btree f (bnil x) := bnil (f x) ;
fmap_btree f (bcons x y) := bcons (fmap_btree f x) (fmap_btree f y).

Global Polymorphic Program Instance btree_Functor : Coq ⟶ Coq := {|
  fmap {f g} := fmap_btree
|}.
Next Obligation.
proper.
revert x1.
fix proper_fmap_btree 1.
destruct x1.

repeat (rewrite fmap_btree_equation_1).
refine (bnil_eq _).
exact (H x1).

repeat (rewrite fmap_btree_equation_2).
refine (bcons_eq _ _).

exact (proper_fmap_btree _).

exact (proper_fmap_btree _).
Defined.

Next Obligation.
revert x0.
fix id_fmap_btree 1.
destruct x0.

rewrite fmap_btree_equation_1.
reflexivity.

rewrite fmap_btree_equation_2.
refine (bcons_eq _ _).
exact (id_fmap_btree _).

exact (id_fmap_btree _).
Defined.

Next Obligation.
revert x0.
fix comp_fmap_btree 1.
destruct x0.

repeat (rewrite fmap_btree_equation_1).
reflexivity.

repeat (rewrite fmap_btree_equation_2).
refine (bcons_eq _ _).

exact (comp_fmap_btree _).

exact (comp_fmap_btree _).
Defined.

