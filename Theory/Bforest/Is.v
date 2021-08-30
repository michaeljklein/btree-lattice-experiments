Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.List.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.
Require Import Embed.Theory.Btree.Zip.
Require Import Embed.Theory.Type.Affine.

Require Import Embed.Theory.Bforest.Zip.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Definition is_bforest {A : Type} (n m : nat) (xs : list (@btree A)) : Prop :=
  n = length xs /\ m = list_num_leaves xs.

Global Program Instance is_bforest_Affine {A} {n m} {xs : list (@btree A)} : Affine (is_bforest n m xs) := {}.
Next Obligation.
destruct x, y.
rewrite (UIP_dec nat_EqDec e e1).
rewrite (UIP_dec nat_EqDec e0 e2).
reflexivity.
Qed.

Fixpoint id_is_bforest {A} (x : A) (n m : nat) : @is_bforest A n n (List.map (fun _ => bnil x) (seq m n)).
split.

rewrite map_length.
rewrite seq_length.
reflexivity.

destruct n.

reflexivity.

simpl.
rewrite list_num_leaves_equation_2.
rewrite num_leaves_equation_1.
simpl.
refine (f_equal _ _).
exact (proj2 (id_is_bforest _ _ _ _)).
Qed.

Equations decompose_btree_is_forest_fst {A} (xs : @btree (@btree A)) :
    is_bforest 1%nat (num_leaves xs) [void xs] :=
decompose_btree_is_forest_fst xs :=
  conj
    eq_refl
    (eq_trans (eq_sym (num_leaves_fmap xs)) (eq_num_leaves_list_num_leaves (void xs))).

Equations decompose_btree_is_forest_snd {A} (xs : @btree (@btree A)) :
    is_bforest (num_leaves xs) (num_leaves (join_btree xs)) (leaves xs) :=
decompose_btree_is_forest_snd xs :=
  conj
    (eq_sym (eq_num_leaves xs))
    (num_leaves_join xs).

Equations map_is_bforest {A B} {n m} {xs : list (@btree A)} (f : A -> B) (xss : @is_bforest A n m xs) :
  @is_bforest B n m (List.map (fmap f) xs) :=
map_is_bforest f (conj pf1 pf2) :=
  conj
    (_ (List.map_length (fmap f) xs))
    (eq_trans pf2 (eq_sym (list_num_leaves_map_fmap _))).

(* Helper for zip_is_bforest *)
Equations zip_is_bforest_length {A B} (x y : nat) (xs : list (@btree A)) (ys : list (@btree B))
 (bs : x = length xs) (cs : y = list_num_leaves xs) (ds : y = length ys) :
 x = length
   (join_zip_btrees xs ys
      (eq_trans (eq_sym cs) ds)) :=
zip_is_bforest_length x y xs ys bs cs ds :=
    eq_trans
      bs
      (eq_sym (length_join_zip_btrees xs ys
        (eq_trans (eq_sym cs) ds)
      )).

(* Helper for zip_is_bforest *)
Equations zip_is_bforest_list_num_leaves {A B} (y z : nat) (xs : list (@btree A)) (ys : list (@btree B))
 (cs : y = list_num_leaves xs) (ds : y = length ys) (es : z = list_num_leaves ys) :
 z =
 list_num_leaves
   (join_zip_btrees xs ys
      (eq_trans (eq_sym cs) ds)) :=
zip_is_bforest_list_num_leaves x y xs ys cs ds es :=
    eq_trans
      es
      (eq_sym
        (list_num_leaves_join_zip_btrees xs ys (eq_trans (eq_sym cs) ds))
      ).

Equations zip_is_bforest {A B} {x y z} {xs : list (@btree A)} {ys : list (@btree B)}
  (xss : @is_bforest A x y xs) (yss : @is_bforest B y z ys) :
  @is_bforest B x z (join_zip_btrees xs ys (eq_trans (eq_sym (proj2 xss)) (proj1 yss))) :=
zip_is_bforest xss yss :=
  conj
    (zip_is_bforest_length x y xs ys (proj1 xss) (proj2 xss) (proj1 yss))
    (zip_is_bforest_list_num_leaves y z xs ys (proj2 xss) (proj1 yss) (proj2 yss)).


Equations is_bforest_btree {A} {m} (xs : list (@btree A)) (xss : is_bforest 1%nat m xs) : @btree A :=
is_bforest_btree nil (conj pf _) with pf => {};
is_bforest_btree (cons x _) _ := x.
Global Transparent is_bforest_btree.

(* Unused *)
Lemma eq_is_bforest_btree {A} {m} (xs ys : list (@btree A))
  (xss : is_bforest 1%nat m xs)
  (yss : is_bforest 1%nat m ys)
  (pf : xs = ys) :
    is_bforest_btree xs xss = is_bforest_btree ys yss.
destruct xs, ys.

destruct xss.
discriminate.

destruct xss.
discriminate.

destruct yss.
discriminate.

destruct xs, ys.

destruct pf.
rewrite (affine xss yss).
reflexivity.

destruct yss.
discriminate.

destruct xss.
discriminate.

destruct xss.
discriminate.
Qed.

Definition btree_is_bforest {A} (xs : @btree A) : is_bforest 1%nat (list_num_leaves (cons xs nil)) (cons xs nil) :=
  conj eq_refl eq_refl.

Lemma iso_is_bforest_btree {A} (xs : @btree A) : is_bforest_btree _ (btree_is_bforest xs) = xs.
Proof.
destruct xs.

unfold btree_is_bforest.
rewrite is_bforest_btree_equation_2.
reflexivity.

unfold btree_is_bforest.
rewrite is_bforest_btree_equation_2.
reflexivity.
Qed.

(* Lemma iso_btree_is_bforest {A} {m} {xs : list (@btree A)} (xss : is_bforest 1%nat m xs) : *)
(*   btree_is_bforest (is_bforest_btree xss) = xss. *)
(* Proof. *)
(*   _ *)
(* Defined. *)

(* Equations decompose_btree_is_forest_fst {A} (xs : @btree (@btree A)) : *)
(*     is_bforest 1%nat (num_leaves (void xs)) (cons (void xs) nil). *)

(* Equations decompose_btree_is_forest_snd {A} (xs : @btree (@btree A)) : *)
(*     is_bforest (num_leaves (void xs)) (list_num_leaves (leaves xs)) (leaves xs). *)

Lemma is_bforest_btree_dep_hd {A} {m} (xs : list (@btree A)) (xss : is_bforest 1%nat m xs) :
  is_bforest_btree xs xss =
    dep_hd xs (fun pf => Lt.lt_0_neq _ PeanoNat.Nat.lt_0_1 (sym_eq (eq_trans (proj1 xss) (f_equal _ pf)))).
destruct xs.

destruct xss.
discriminate.

reflexivity.
Qed.

Corollary is_bforest_btree_hd {A} {m} (xs : list (@btree A)) (xss : is_bforest 1%nat m xs)
  (ys : @btree A) :
    is_bforest_btree xs xss = hd ys xs.
exact (eq_trans (is_bforest_btree_dep_hd xs xss) (eq_dep_hd xs _ ys)).
Qed.

