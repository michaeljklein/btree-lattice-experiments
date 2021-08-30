Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Lattice.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Notation "btree!" := (@btree ()) (only parsing, at level 0).
Notation "bnil!" := (@bnil () tt) (only parsing, at level 0).
Notation "btree2!" := (@btree () * @btree ()) (only parsing, at level 0).

Equations and_btree : magma btree! :=
and_btree (bnil _) (bnil _) := bnil () ;
and_btree (bnil _) (bcons _ _) := bnil () ;
and_btree (bcons _ _) (bnil x) := bnil () ;
and_btree (bcons x y) (bcons z w) := bcons (and_btree x z) (and_btree y w).
Global Transparent and_btree.

Global Program Instance and_btree_Idempotent : Idempotent and_btree :=
  { idempotency := _ }.
Next Obligation.
revert x.
fix H 1.
intro.
destruct x.

rewrite and_btree_equation_1.
destruct u.
reflexivity.

rewrite and_btree_equation_4.
refine (bcons_eq _ _).

exact (@idempotency _ _ H _).

exact (@idempotency _ _ H _).
Defined.

Program Instance and_btree_Commutative : Commutative and_btree :=
  { commutativity := _ }.
Next Obligation.
revert b. revert a.
fix and_btree_Commutative 2.
intros.
destruct a, b.

reflexivity.

reflexivity.

reflexivity.

exact (bcons_eq (and_btree_Commutative _ _) (and_btree_Commutative _ _)).
Defined.

Fixpoint and_btree_associative (a b c : btree!) :
  and_btree (and_btree a b) c = and_btree a (and_btree b c).
destruct a, b, c.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

unfold and_btree.
refine (bcons_eq _ _).

exact (and_btree_associative _ _ _).

exact (and_btree_associative _ _ _).
Defined.

(* Fails with fix *)
Program Instance and_btree_Associative : Associative and_btree :=
  { associativity := and_btree_associative }.

Equations or_btree : magma btree! :=
or_btree (bnil _) (bnil _) := bnil tt ;
or_btree (bcons x y) (bnil _) := bcons x y ;
or_btree (bnil _) (bcons x y) := bcons x y ;
or_btree (bcons x y) (bcons z w) := bcons (or_btree x z) (or_btree y w).
Global Transparent or_btree.

(* Almost the same proof as for and_btree *)
Program Instance or_btree_Idempotent : Idempotent or_btree :=
  { idempotency := _ }.
Next Obligation.
revert x.
fix H 1.
intro.
destruct x.

rewrite or_btree_equation_1.
destruct u.
reflexivity.

rewrite or_btree_equation_4.
refine (bcons_eq _ _).

exact (@idempotency _ _ H _).

exact (@idempotency _ _ H _).
Defined.

(* Almost the same proof as for and_btree *)
Program Instance or_btree_Commutative : Commutative or_btree :=
  { commutativity := _ }.
Next Obligation.
revert b. revert a.
fix or_btree_Commutative 2.
intros.
destruct a, b.

reflexivity.

reflexivity.

reflexivity.

exact (bcons_eq (or_btree_Commutative _ _) (or_btree_Commutative _ _)).
Defined.

(* Almost the same proof as for and_btree *)
Fixpoint or_btree_associative (a b c : btree!) :
  or_btree (or_btree a b) c = or_btree a (or_btree b c).
destruct a, b, c.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

reflexivity.

unfold or_btree.
refine (bcons_eq _ _).

exact (or_btree_associative _ _ _).

exact (or_btree_associative _ _ _).
Defined.

Program Instance or_btree_Associative : Associative or_btree :=
  { associativity := or_btree_associative }.

Fixpoint and_or_absorptive (a b : btree!) :
  and_btree a (or_btree a b) = a.
destruct a, b.

unfold or_btree.
unfold and_btree.
destruct u.
reflexivity.

unfold or_btree.
unfold and_btree.
destruct u.
reflexivity.

unfold or_btree.
unfold and_btree.
refine (bcons_eq _ _).

exact (@idempotency _ _ and_btree_Idempotent _).

exact (@idempotency _ _ and_btree_Idempotent _).

unfold or_btree.
unfold and_btree.
refine (bcons_eq _ _).

exact (and_or_absorptive a1 b1).

exact (and_or_absorptive a2 b2).
Defined.

(* May not need Fixpoint, but doesn't allow funelim *)
Program Instance and_or_Absorptive :
  Absorptive and_btree or_btree := { absorptivity := and_or_absorptive }.

(* Almost the same proof as for and_or_absorptive *)
Fixpoint or_and_absorptive (a b : btree!) :
  or_btree a (and_btree a b) = a.
destruct a, b.

unfold or_btree.
unfold and_btree.
destruct u.
reflexivity.

unfold or_btree.
unfold and_btree.
destruct u.
reflexivity.

unfold or_btree.
unfold and_btree.
refine (bcons_eq _ _).

reflexivity.

reflexivity.

rewrite and_btree_equation_4.
rewrite or_btree_equation_4.
refine (bcons_eq _ _).

exact (or_and_absorptive a1 b1).

exact (or_and_absorptive a2 b2).
Defined.

Program Instance or_and_Absorptive :
  Absorptive or_btree and_btree := { absorptivity := or_and_absorptive }.

Program Instance btree_unit_Lattice : Lattice btree := {
  lmeet := and_btree;
  ljoin := or_btree;

  lmeet_commutative := and_btree_Commutative;
  lmeet_associative := and_btree_Associative;
  lmeet_absorptive  := and_or_Absorptive;
  lmeet_idempotent  := and_btree_Idempotent;

  ljoin_commutative := or_btree_Commutative;
  ljoin_associative := or_btree_Associative;
  ljoin_absorptive  := or_and_Absorptive;
  ljoin_idempotent  := or_btree_Idempotent
}.


Fixpoint and_or_distributive (a b c : btree!) :
  and_btree a (or_btree b c) = or_btree (and_btree a b) (and_btree a c).
destruct a, b, c.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
reflexivity.

unfold or_btree.
unfold and_btree.
refine (bcons_eq _ _).

exact (and_or_distributive _ _ _).

exact (and_or_distributive _ _ _).
Defined.

Program Instance and_or_Distributive :
  Distributive and_btree or_btree := { distributivity := and_or_distributive }.

Obligations.
