Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Embed.Theory.Btree.

Require Import Equations.Type.Logic.
Require Import Equations.Type.Classes.
Require Import Equations.Type.Loader.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section BtreeEquationsClasses.

Import Sigma_Notations.
Import Id_Notations.
Local Open Scope equations_scope.

(* TODO: why is this not imported properly? *)
Derive NoConfusion for btree.

Equations distribute_id_bnil {A} {x y : A} (xs : bnil x = bnil y) : x = y :=
distribute_id_bnil id_refl := id_refl.

Equations distribute_id_bcons {A} {x y z w : @btree A} (xs : bcons x y = bcons z w) : Datatypes.prod (x = z) (y = w) :=
distribute_id_bcons id_refl := pair id_refl id_refl.

Equations lift_id_bnil {A} {x y : A} :
  (x = y) + (x <> y) ->
  (bnil x = bnil y) + (bnil x <> bnil y) :=
lift_id_bnil (Logic.inl id_refl) := Logic.inl id_refl;
lift_id_bnil (Logic.inr pfXY) := Logic.inr (fun pfXYs => pfXY (distribute_id_bnil pfXYs)).

Equations lift_id_bcons {A} {x y z w : @btree A} :
  (x = y) + (x <> y) ->
  (z = w) + (z <> w) ->
  (bcons x z = bcons y w) + (bcons x z <> bcons y w) :=
lift_id_bcons (Logic.inl id_refl) (Logic.inl id_refl) := Logic.inl id_refl ;
lift_id_bcons (Logic.inl id_refl) (Logic.inr pfZW) :=
  Logic.inr (fun idXZW => pfZW (snd (distribute_id_bcons idXZW))) ;
lift_id_bcons (Logic.inr pfXY) (Logic.inl id_refl) :=
  Logic.inr (fun idXZY => pfXY (fst (distribute_id_bcons idXZY))) ;
lift_id_bcons (Logic.inr pfXY) (Logic.inr _) :=
  Logic.inr (fun pfXZYW => pfXY (fst (distribute_id_bcons pfXZYW))).

Lemma not_bnil_id_bcons : forall
  (A : Set)
  (wildcard : A)
  (xs ys : btree@{Set})
  (H : bnil@{Set} wildcard = bcons@{Set} xs ys), Empty.
intros.
inversion H.
Qed.

Lemma not_bcons_id_bnil : forall
  (A : Set)
  (wildcard : A)
  (xs ys : btree@{Set})
  (H : bcons@{Set} xs ys = bnil@{Set} wildcard), Empty.
intros.
inversion H.
Qed.

Equations dec_id_btree {A} {EqDecA : Classes.EqDec A} : Classes.EqDec (@btree A) :=
dec_id_btree (bnil xs) (bnil ys) := lift_id_bnil (EqDecA xs ys) ;
dec_id_btree (bnil _) (bcons xs ys) := Logic.inr (not_bnil_id_bcons _ _ _ _) ;
dec_id_btree (bcons xs ys) (bnil _) := Logic.inr (not_bcons_id_bnil _ _ _ _) ;
dec_id_btree (bcons xs ys) (bcons zs ws) := lift_id_bcons (dec_id_btree xs zs) (dec_id_btree ys ws).

Program Instance eqdec_btree {A : Type} `{eqDecA : Classes.EqDec A} : Classes.EqDec (@btree A) := {
  Classes.eq_dec := dec_id_btree
}.


Program Instance uip_btree {A : Type} `{eqDecA : Classes.EqDec A} : Classes.UIP (@btree A) := {}.
Next Obligation.
exact (Classes.UIP_hSet btree (EqDecInstances.eqdec_hset btree eqdec_btree) _ _ _ _).
Qed.

Local Close Scope equations_scope.

End BtreeEquationsClasses.

