Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Type.Positive.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

(* TODO: Move to Utils *)
Equations pair_eq {A B} {x z : A} {y w : B} (xz : x = z) (yw : y = w) : pair x y = pair z w :=
pair_eq eq_refl eq_refl := eq_refl.

Equations pair_iso_to {x y z w} (xz : x ≅ z) (yw : y ≅ w) :
  prod x y -> prod z w :=
pair_iso_to xz yw (pair x' y') := pair (to xz x') (to yw y').

Equations pair_iso_from {x y z w} (xz : x ≅ z) (yw : y ≅ w) :
  prod z w -> prod x y :=
pair_iso_from xz yw (pair x' y') := pair (from xz x') (from yw y').

Polymorphic Program Instance pair_iso {x y z w} (xz : x ≅ z) (yw : y ≅ w) :
  prod x y ≅ prod z w := {
    to   := pair_iso_to _ _;
    from := pair_iso_from _ _
}.
Next Obligation.
rewrite pair_iso_from_equation_1.
rewrite pair_iso_to_equation_1.
destruct xz, yw.
simpl.
pose (H := iso_to_from z0).
simpl in H.
rewrite H.
clear H.
pose (H := iso_to_from0 w0).
simpl in H.
rewrite H.
reflexivity.
Qed.

(* Almost the same proof as above *)
Next Obligation.
rewrite pair_iso_to_equation_1.
rewrite pair_iso_from_equation_1.
destruct xz, yw.
simpl.
pose (H := iso_from_to x0).
simpl in H.
rewrite H.
clear H.
pose (H := iso_from_to0 y0).
simpl in H.
rewrite H.
reflexivity.
Qed.

(* TODO: move to Utils: similar to let_fst, let_snd from Category.Lib.Datatypes *)
Corollary let_fst_snd {x y z} (A : x * y) `(f : x -> y -> z) :
  (let (x, y) := A in f x y) = f (fst A) (snd A).
Proof. destruct A; auto. Qed.

Equations abstract_prod_l_to {x y z}
  (iso : y ≅ z) : x * y -> x * z :=
abstract_prod_l_to iso (pair xs ys) := pair xs (to iso ys).

Equations abstract_prod_l_from {x y z}
  (iso : y ≅ z) : x * z -> x * y :=
abstract_prod_l_from iso (pair xs ys) := pair xs (from iso ys).

Polymorphic Program Instance abstract_prod_l {x y z}
  (iso : y ≅ z) : x * y ≅ x * z := {
    to   := abstract_prod_l_to iso;
    from := abstract_prod_l_from iso
}.
Next Obligation.
rewrite abstract_prod_l_from_equation_1.
rewrite abstract_prod_l_to_equation_1.
refine (pair_eq eq_refl _).
exact (iso_to_from iso z0).
Qed.

Next Obligation.
rewrite abstract_prod_l_to_equation_1.
rewrite abstract_prod_l_from_equation_1.
refine (pair_eq eq_refl _).
exact (iso_from_to iso y0).
Qed.

(* Print iso_refined. *)

Class Iso_prod_id_l {A B C : Type}
  (iso : A ∧ B ≅ A ∧ C) : Type := {
    iso_prod_id_l_to :
      forall (x : A) (y : B),
        fst (to iso (pair x y)) = x;
    iso_prod_id_l_from :
      forall (x : A) (y : C),
        fst (from iso (pair x y)) = x
}.

Equations refine_iso_prod_id_l_to {A B C : Type}
  {positiveA : Positive A}
  (iso : A ∧ B ≅ A ∧ C) : B -> C :=
refine_iso_prod_id_l_to iso x :=
  snd (to iso (pair positive x)).

Equations refine_iso_prod_id_l_from {A B C : Type}
  {positiveA : Positive A}
  (iso : A ∧ B ≅ A ∧ C) : C -> B :=
refine_iso_prod_id_l_from iso x :=
  snd (from iso (pair positive x)).

Program Instance refine_iso_prod_id_l {A B C : Type}
  {positiveA : Positive A}
  (iso : A ∧ B ≅ A ∧ C)
  {pf : Iso_prod_id_l iso} : B ≅ C := {
    to   := refine_iso_prod_id_l_to iso;
    from := refine_iso_prod_id_l_from iso
}.
Next Obligation.
rewrite refine_iso_prod_id_l_from_equation_1.
rewrite refine_iso_prod_id_l_to_equation_1.
destruct pf.
replace (positive, snd (from iso (positive, x))) with
        (fst (from iso (positive, x)), snd (from iso (positive, x))) by
(exact (pair_eq
  (iso_prod_id_l_from0 positive x)
  eq_refl
)).
rewrite <- surjective_pairing.
pose (H := (iso_to_from iso (positive, x))).
simpl in H.
rewrite H.
simpl.
reflexivity.
Qed.

Next Obligation.
rewrite refine_iso_prod_id_l_from_equation_1.
rewrite refine_iso_prod_id_l_to_equation_1.
destruct pf.
replace (positive, snd (to iso (positive, x))) with
        (fst (to iso (positive, x)), snd (to iso (positive, x))) by
(exact (pair_eq
  (iso_prod_id_l_to0 positive x)
  eq_refl
)).
rewrite <- surjective_pairing.
pose (H := (iso_from_to iso (positive, x))).
simpl in H.
rewrite H.
simpl.
reflexivity.
Qed.

Equations to_Iso_prod_id_l_bool_to {B C : Type}
  (iso : bool ∧ B ≅ bool ∧ C) : bool ∧ B -> bool ∧ C :=
to_Iso_prod_id_l_bool_to iso (pair true x) with (fst (to iso (pair true x))) => {
  to_Iso_prod_id_l_bool_to iso (pair true x) true :=
    to iso (pair true x);
  to_Iso_prod_id_l_bool_to iso (pair true x) false :=
    to iso (from iso (pair false (snd (to iso (pair true x)))))
};
to_Iso_prod_id_l_bool_to iso (pair false x) with (fst (to iso (pair false x))) => {
  to_Iso_prod_id_l_bool_to iso (pair false x) true :=
    to iso (from iso (pair true (snd (to iso (pair false x)))));
  to_Iso_prod_id_l_bool_to iso (pair false x) false :=
    to iso (pair false x)
}.

Equations to_Iso_prod_id_l_bool_from {B C : Type}
  (iso : bool ∧ B ≅ bool ∧ C) : bool ∧ C -> bool ∧ B :=
to_Iso_prod_id_l_bool_from iso (pair true x) with (fst (from iso (pair true x))) => {
  to_Iso_prod_id_l_bool_from iso (pair true x) true :=
    from iso (pair true x);
  to_Iso_prod_id_l_bool_from iso (pair true x) false :=
    from iso (to iso (pair false (snd (from iso (pair true x)))))
};
to_Iso_prod_id_l_bool_from iso (pair false x) with (fst (from iso (pair false x))) => {
  to_Iso_prod_id_l_bool_from iso (pair false x) true :=
    from iso (to iso (pair true (snd (from iso (pair false x)))));
  to_Iso_prod_id_l_bool_from iso (pair false x) false :=
    from iso (pair false x)
}.

