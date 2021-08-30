Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Functor.Refined.Iso.
Require Import Embed.Theory.Datatypes.Prod.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Canonical.
Require Import Embed.Theory.Btree.Leaves.

Require Import Embed.Theory.Btree.Refined.Iso.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.


Fixpoint iso_refined_canonical_btree_plus (x y : nat) : forall (A : Type),
  refined (canonical_btree (S x + y)) A ≅
    refined (canonical_btree x) A ∧ refined (canonical_btree y) A.
intro.
destruct x.

rewrite canonical_btree_equation_2.
rewrite canonical_btree_equation_1.
exact (refined_bcons _ _ A).

rewrite canonical_btree_equation_2.
replace (S (S x) + y)%nat with (S (S x + y))%nat.

rewrite canonical_btree_equation_2.
refine (iso_compose _ (refined_bcons (bnil tt) (canonical_btree (S x + y)) A)).
refine (iso_compose (iso_sym (@pair_iso
  (refined (bcons (bnil tt) (canonical_btree x)) A)
  (refined (canonical_btree y) A)
  (refined (bnil tt) A ∧ refined (canonical_btree x) A)
  (refined (canonical_btree y) A)
  _
  iso_id
)) _).
refine (iso_compose (iso_sym (@prod_assoc Coq Coq_Cartesian
  (refined (bnil ()) A)
  (refined (canonical_btree x) A)
  (refined (canonical_btree y) A)
)) _).

reflexivity.

Qed.

Fixpoint iso_refined_canonical_btree (x : @btree 1) :
  iso_refined x (canonical_btree (pred (num_leaves x))).
unfold iso_refined.
intro.
destruct x.

rewrite num_leaves_equation_1.
simpl.
rewrite canonical_btree_equation_1.
destruct t.
exact iso_id.

rewrite num_leaves_equation_2.
pose (x1' := iso_refined_canonical_btree x1 A).
pose (x2' := iso_refined_canonical_btree x2 A).
refine (iso_compose _ (refined_bcons x1 x2 A)).
replace (pred (num_leaves x1 + num_leaves x2))%nat with
        (S (pred (num_leaves x1)) + pred (num_leaves x2))%nat.
2: {
  simpl.
  replace (S (pred (num_leaves x1) + pred (num_leaves x2)))%nat with
          (S (pred (num_leaves x1)) + pred (num_leaves x2))%nat by reflexivity.
  pose (H := f_equal
    (fun x => x + pred (num_leaves x2))%nat
    (PeanoNat.Nat.succ_pred (num_leaves x1) (num_leaves_positive x1))
  ).
  simpl in H.
  rewrite H.
  clear H.
  pose (H := PeanoNat.Nat.add_pred_r (num_leaves x1) (num_leaves x2) (num_leaves_positive x2)).
  simpl in H.
  rewrite H.
  reflexivity.
}

refine (iso_compose
  (iso_sym
    (iso_refined_canonical_btree_plus (pred (num_leaves x1)) (pred (num_leaves x2)) A)
  )
  _
).
Qed.

