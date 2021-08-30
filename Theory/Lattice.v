Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Definition magma (A : Type) := A -> A -> A.

Class Idempotent {A} (f : magma A) :=
  idempotency : forall (x : A), f x x = x.

(* Search "Commutative". *)
Class Commutative {A} (f : magma A) :=
  commutativity : forall a b, f a b = f b a.

(* Search "Associative". *)
Class Associative {A} (f : magma A) :=
  associativity : forall a b c : A, f (f a b) c = f a (f b c).

(* Search "Absorptive". *)
Class Absorptive {A} (f g : magma A) :=
  absorptivity : forall a b : A, f a (g a b) = a.

(* x ∧ (y ∨ c) = (x ∧ y) ∨ (x ∧ c). *)
Class Distributive {A} (f g : magma A) :=
  distributivity : forall a b c : A, f a (g b c) = g (f a b) (f a c).

Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "⊔" (at level 36, left associativity).

Class Lattice (A : Type) := {
  lmeet : A -> A -> A where "x ⊓ y" := (lmeet x y);
  ljoin : A -> A -> A where "x ⊔ y" := (ljoin x y);

  lmeet_commutative : Commutative lmeet;
  lmeet_associative : Associative lmeet;
  lmeet_absorptive  : Absorptive lmeet ljoin;
  lmeet_idempotent  : Idempotent lmeet;

  ljoin_commutative : Commutative ljoin;
  ljoin_associative : Associative ljoin;
  ljoin_absorptive  : Absorptive ljoin lmeet;
  ljoin_idempotent  : Idempotent ljoin
}.

Program Instance magma_unit_Idempotent (f : magma ()) :
  Idempotent f := { idempotency := _ }.
Next Obligation.
destruct x.
refine (unit_ind (fun xs => xs = ()) _ (f () ())).
reflexivity.
Defined.

Program Instance magma_unit_Commutative (f : magma ()) :
  Commutative f := { commutativity := _ }.

Program Instance magma_unit_Associative (f : magma ()) :
  Associative f := { associativity := _ }.
Next Obligation.
refine (unit_ind (fun xs => xs = f a (f b c)) _ (f (f a b) c)).
refine (unit_ind (fun xs => () = xs) _ (f a (f b c))).
reflexivity.
Defined.

Program Instance magma_unit_Absorptive (f : magma ()) (g : magma ()) :
  Absorptive f g := { absorptivity := _ }.
Next Obligation.
destruct a, b.
refine (unit_ind (fun xs => xs = ()) _ (f () (g () ()))).
reflexivity.
Defined.

Program Instance magma_unit_Distributive (f : magma ()) (g : magma ()) :
  Distributive f g := { distributivity := _ }.
Next Obligation.
refine (unit_ind (fun xs => f a (g b c) = xs) _ (g (f a b) (f a c))).
refine (unit_ind (fun xs => xs = ()) _ (f a (g b c))).
reflexivity.
Defined.

Program Instance magma_unit_Lattice (f g : magma ()) : Lattice () := {
  lmeet := f;
  ljoin := g;

  lmeet_commutative := magma_unit_Commutative _;
  lmeet_associative := magma_unit_Associative _;
  lmeet_absorptive  := magma_unit_Absorptive _ _;
  lmeet_idempotent  := magma_unit_Idempotent _;

  ljoin_commutative := magma_unit_Commutative _;
  ljoin_associative := magma_unit_Associative _;
  ljoin_absorptive  := magma_unit_Absorptive _ _;
  ljoin_idempotent  := magma_unit_Idempotent _
}.


