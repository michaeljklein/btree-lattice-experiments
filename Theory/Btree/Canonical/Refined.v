Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FinFun.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Functor.Refined.Iso.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Canonical.
Require Import Embed.Theory.Btree.Canonical.Refined.Enumerate.
(* Require Import Embed.Theory.Btree.Functor. *)

Require Import Embed.Theory.Datatypes.List.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Lemma to_iso_Injective {A B : Type} (iso : A ≅ B) : Injective (to iso).
proper.
pose (H' := f_equal (from iso) H).
pose (iso_from_to iso x).
simpl in e.
rewrite e in H'.
pose (iso_from_to iso y).
simpl in e0.
rewrite e0 in H'.
exact H'.
Qed.

Lemma iso_refined_canonical_btree_le (x y : nat) :
  iso_refined (canonical_btree x) (canonical_btree y) ->
  (length (enumerate_refined_canonical_btree_bool x) <=
   length (enumerate_refined_canonical_btree_bool y))%nat.
intro.
pose (iso_bool := X bool).
pose (to_iso_bool_Injective := to_iso_Injective iso_bool).
pose (xs := enumerate_refined_canonical_btree_bool x).
pose (nodup_xs := enumerate_refined_canonical_btree_bool_nodup x).
pose (ys := List.map (to iso_bool) xs).
pose (nodup_ys := @Injective_map_NoDup
  _
  _
  (to iso_bool)
  xs
  to_iso_bool_Injective
  nodup_xs
).
pose (le_ys_y := @nodup_pigeonhole _
  (@refined_EqDec _
    (canonical_btree y)
    (@dec_eq_btree 1 unit_EqDec)
    bool
    (@dec_eq_btree bool bool_EqDec)
  )
  ys
  (enumerate_refined_canonical_btree_bool y)
  nodup_ys
  (Full_to_AllIn _ _ (enumerate_refined_canonical_btree_bool_all y))
).
unfold ys in le_ys_y.
rewrite (List.map_length (to iso_bool)) in le_ys_y.
unfold xs in le_ys_y.
exact le_ys_y.
Qed.

Theorem iso_refined_canonical_btree_eq (x y : nat) :
  iso_refined (canonical_btree x) (canonical_btree y) -> x = y.
intro.
pose (xy := iso_refined_canonical_btree_le x y X).
pose (yx := iso_refined_canonical_btree_le y x
  (@Equivalence_Symmetric _ _ equiv_iso_refined _ _ X)
).
pose (eq_length_xy := PeanoNat.Nat.le_antisymm _ _ xy yx).
exact (enumerate_refined_canonical_btree_bool_length_eq _ _ eq_length_xy).
Qed.

