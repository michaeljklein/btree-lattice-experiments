Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Canonical.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Definition list_of_length (n : nat) (A : Type) :=
  { x : list A | n = length x }.

Equations cons_list_of_length {n : nat} {A : Type} : A -> list_of_length n A -> list_of_length (S n) A :=
cons_list_of_length x (@exist _ _ xs _) := @exist _ _ (cons x xs) _.

Equations uncons_list_of_length {n : nat} {A : Type} : list_of_length (S n) A -> A * list_of_length n A :=
uncons_list_of_length (@exist _ _ nil _) := _;
uncons_list_of_length (@exist _ _ (cons x xs) _) := pair x (@exist _ _ xs _).

Lemma cons_refined_canonical_btree_pf {n : nat} {A : Type} (x : A) (xs : @btree A)
  (pf : Void.void xs = canonical_btree n) :
    Void.void (bcons (bnil x) xs) = canonical_btree (S n).
rewrite canonical_btree_equation_2.
unfold Void.void.
rewrite fmap_btree_equation_2.
rewrite fmap_btree_equation_1.
exact (bcons_eq eq_refl pf).
Qed.

Equations cons_refined_canonical_btree {n : nat} {A : Type} :
  A -> refined (canonical_btree n) A -> refined (canonical_btree (S n)) A :=
cons_refined_canonical_btree x (@exist _ _ xs pf) :=
  @exist _ _ (bcons (bnil x) xs) (cons_refined_canonical_btree_pf x xs pf).


Equations refined_canonical_btree_iso_list_to (n : nat) (A : Type) :
  refined (canonical_btree n) A -> list_of_length (S n) A :=
refined_canonical_btree_iso_list_to O _ (@exist _ _ (bnil x) _) :=
  @exist _ _ (cons x nil) eq_refl;
refined_canonical_btree_iso_list_to O _ (@exist _ _ (bcons  _ _) _) := _;
refined_canonical_btree_iso_list_to (S _) _ (@exist _ _ (bnil _) _) := _;
refined_canonical_btree_iso_list_to (S n) A (@exist _ _ (bcons (bnil x) xs) _) :=
  cons_list_of_length x (refined_canonical_btree_iso_list_to n A (@exist _ _ xs _)) ;
refined_canonical_btree_iso_list_to (S _) _ (@exist _ _ (bcons (bcons _ _) _) _) := _.

Lemma refined_canonical_btree_iso_list_to_cons (n : nat) (A : Type)
  (x : A) (xs : refined (canonical_btree n) A) :
    refined_canonical_btree_iso_list_to (S n) A
      (cons_refined_canonical_btree x xs) =
        cons_list_of_length x (refined_canonical_btree_iso_list_to n A xs).
destruct xs.
destruct n.

destruct x0.
2: {
  discriminate.
}
rewrite cons_refined_canonical_btree_equation_1.
rewrite refined_canonical_btree_iso_list_to_equation_4.
repeat (rewrite refined_canonical_btree_iso_list_to_equation_1).
reflexivity.

destruct x0.
1: {
  discriminate.
}
Local Transparent canonical_btree.
simpl in e.
Local Opaque canonical_btree.
Local Transparent fmap_btree.
simpl in e.
Local Opaque fmap_btree.
destruct x0_1.
2: {
  discriminate.
}
rewrite cons_refined_canonical_btree_equation_1.
repeat (rewrite refined_canonical_btree_iso_list_to_equation_4).
refine (f_equal (cons_list_of_length x) _).
refine (f_equal (cons_list_of_length a) _).
refine (f_equal (refined_canonical_btree_iso_list_to n A) _).
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
exact (UIP_dec dec_eq_btree _ _).
Qed.

Equations refined_canonical_btree_iso_list_from (n : nat) (A : Type) :
  list_of_length (S n) A -> refined (canonical_btree n) A :=
refined_canonical_btree_iso_list_from O _ (@exist _ _ nil _) := _;
refined_canonical_btree_iso_list_from O _ (@exist _ _ (cons x _) _) :=
  @exist _ _ (bnil x) _;
refined_canonical_btree_iso_list_from (S _) _ (@exist _ _ nil _) := _;
refined_canonical_btree_iso_list_from (S n) A (@exist _ _ (cons x xs) _) :=
  cons_refined_canonical_btree x (refined_canonical_btree_iso_list_from n A (@exist _ _ xs _)).

Lemma refined_canonical_btree_iso_list_from_cons (n : nat) (A : Type)
  (x : A) (xs : list_of_length (S n) A) :
    refined_canonical_btree_iso_list_from (S n) A
      (cons_list_of_length x xs) =
        cons_refined_canonical_btree x (refined_canonical_btree_iso_list_from n A xs).
destruct xs.
destruct n.

destruct x0.
1: {
  discriminate.
}
destruct x0.
2: {
  discriminate.
}
rewrite cons_list_of_length_equation_1.
rewrite refined_canonical_btree_iso_list_from_equation_4.
refine (f_equal _ _).
refine (f_equal _ _).
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
exact (UIP_dec nat_EqDec _ _).

destruct x0.
1: {
  discriminate.
}
simpl in e.

rewrite cons_list_of_length_equation_1.
rewrite refined_canonical_btree_iso_list_from_equation_4.
refine (f_equal _ _).
refine (f_equal _ _).
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
exact (UIP_dec nat_EqDec _ _).
Qed.

Fixpoint refined_canonical_btree_iso_list_to_from (n : nat) (A : Type)
  (x : list_of_length (S n) A) :
    refined_canonical_btree_iso_list_to n A
      (refined_canonical_btree_iso_list_from n A x) = x.
destruct n.
destruct x.

destruct x.
1: {
  discriminate.
}
destruct x.
2: {
  discriminate.
}
simpl in e.
rewrite refined_canonical_btree_iso_list_from_equation_2.
rewrite refined_canonical_btree_iso_list_to_equation_1.
rewrite (UIP_dec nat_EqDec e eq_refl).
reflexivity.

destruct x.
destruct x.
1: {
  discriminate.
}
simpl in e.

rewrite refined_canonical_btree_iso_list_from_equation_4.
rewrite refined_canonical_btree_iso_list_to_cons.
rewrite (refined_canonical_btree_iso_list_to_from n A
  (exist (λ x0 : list A, S n = length x0) x
           (refined_canonical_btree_iso_list_from_obligations_obligation_4
              refined_canonical_btree_iso_list_from n A a x e))
).
rewrite cons_list_of_length_equation_1.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
exact (UIP_dec nat_EqDec _ _).
Qed.

Fixpoint refined_canonical_btree_iso_list_from_to (n : nat) (A : Type)
  (x : refined (canonical_btree n) A) :
    refined_canonical_btree_iso_list_from n A
      (refined_canonical_btree_iso_list_to n A x) = x.
destruct n.
destruct x.

destruct x.
2: {
  discriminate.
}
rewrite refined_canonical_btree_iso_list_to_equation_1.
rewrite refined_canonical_btree_iso_list_from_equation_2.
rewrite (UIP_dec dec_eq_btree e eq_refl).
reflexivity.

destruct x.
destruct x.
1: {
  discriminate.
}
Local Transparent canonical_btree.
simpl in e.
Local Opaque canonical_btree.
destruct x1.
2: {
  discriminate.
}
rewrite refined_canonical_btree_iso_list_to_equation_4.
rewrite refined_canonical_btree_iso_list_from_cons.
rewrite refined_canonical_btree_iso_list_from_to.
rewrite cons_refined_canonical_btree_equation_1.
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
exact (UIP_dec dec_eq_btree _ _).
Qed.

Program Instance refined_canonical_btree_iso_list (n : nat) (A : Type) :
  refined (canonical_btree n) A ≅ list_of_length (S n) A := {
    to   := refined_canonical_btree_iso_list_to n A;
    from := refined_canonical_btree_iso_list_from n A;

    iso_to_from := refined_canonical_btree_iso_list_to_from n A;
    iso_from_to := refined_canonical_btree_iso_list_from_to n A
}.

