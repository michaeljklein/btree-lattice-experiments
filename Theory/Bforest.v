Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.
Require Import Embed.Theory.Btree.Zip.
Require Import Embed.Theory.Bforest.Zip.
Require Import Embed.Theory.Bforest.Is.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.List.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

(* A bforest is isomorphic to the "last btree" in a finite composition of *)
(* btree's: [ @btree (@btree (@btree ..)) ]. *)
Definition bforest {A : Type} (n m : nat) : Type :=
  { xs : list (@btree A) | is_bforest n m xs}.

Lemma eq_bforest {A} {n m : nat}
  (xs : @bforest A n m)
  (ys : @bforest A n m)
  (pfx : proj1_sig xs = proj1_sig ys) :
    xs = ys.
destruct xs, ys.
refine (eq_sig
  (exist (λ xs : list btree, is_bforest n m xs) x i)
  (exist (λ xs : list btree, is_bforest n m xs) x0 i0)
  pfx
  _
).
simpl in *.
destruct pfx.
simpl.
exact (is_bforest_Affine _ _).
Qed.

Equations id_bforest {A : Type} (x : A) (n : nat) : @bforest A n n :=
id_bforest x n := exist _ _ (id_is_bforest x n 0%nat).

Equations decompose_btree_fst {A} (xs : @btree (@btree A)) :
  @bforest () 1%nat (num_leaves xs) :=
decompose_btree_fst xs :=
  exist _ _ (decompose_btree_is_forest_fst xs).

Equations decompose_btree_snd {A} (xs : @btree (@btree A)) :
  @bforest A (num_leaves xs) (num_leaves (join_btree xs)) :=
decompose_btree_snd xs :=
  exist _ (leaves xs) (decompose_btree_is_forest_snd xs).

Equations trans_bforest {A B} {x y z} (xy : @bforest A x y) (yz : @bforest B y z) :
  @bforest B x z :=
trans_bforest (exist _ _ xy) (exist _ _ yz) := exist _ _ (zip_is_bforest xy yz).

Equations bforest_btree {A} {m} (xs : @bforest A 1%nat m) : @btree A :=
bforest_btree (exist _ _ xss) := is_bforest_btree _ xss.

Equations btree_bforest {A} (xs : @btree A) : @bforest A 1%nat (list_num_leaves (cons xs nil)) :=
btree_bforest xs := exist _ _ (btree_is_bforest xs).

(* (1* This gives us an isomorphism with the free monad over btree, *1) *)
(* (1* including identity and associativity. *1) *)
(* Lemma trans_decompose_bforest {A} (xs : @btree (@btree A)) : *)
(*   bforest_btree (trans_bforest (decompose_btree_fst xs) (decompose_btree_snd xs)) = join_btree xs. *)
(* rewrite decompose_btree_fst_equation_1. *)
(* rewrite decompose_btree_snd_equation_1. *)
(* rewrite trans_bforest_equation_1. *)
(* rewrite bforest_btree_equation_1. *)
(* exact (zip_decompose_btree_is_bforest xs). *)
(* Qed. *)

Program Instance BforestC : Category := {
  obj     := nat ;

  hom     := fun n m : nat => @bforest () n m ;

  homset  := fun _ _ => {| equiv := eq |} ;

  id      := id_bforest tt ;

  compose := fun _ _ _ => Basics.flip trans_bforest
}.
Next Obligation.
unfold Basics.flip.
destruct f.
rewrite id_bforest_equation_1.
rewrite trans_bforest_equation_1.
refine (eq_bforest _ _ _).
simpl.
destruct i.
rewrite e.
rewrite e0.
exact (join_zip_btrees_id_l _).
Qed.

Next Obligation.
unfold Basics.flip.
destruct f.
rewrite id_bforest_equation_1.
rewrite trans_bforest_equation_1.
refine (eq_bforest _ _ _).
simpl.
destruct i.
rewrite e.
rewrite e0.
exact (join_zip_btrees_id_r _).
Qed.

Next Obligation.
unfold Basics.flip.
destruct f, g, h.
destruct i, i0, i1.
repeat (rewrite trans_bforest_equation_1).
refine (eq_bforest _ _ _).
simpl.
repeat (rewrite e || rewrite e0 || rewrite e1 || rewrite e2 || rewrite e3 || rewrite e4).
exact (assoc_join_zip_btrees _ _ _ _).
Qed.

Next Obligation.
unfold Basics.flip.
destruct f, g, h.
destruct i, i0, i1.
repeat (rewrite trans_bforest_equation_1).
refine (eq_bforest _ _ _).
simpl.
repeat (rewrite e || rewrite e0 || rewrite e1 || rewrite e2 || rewrite e3 || rewrite e4).
exact (eq_sym (assoc_join_zip_btrees _ _ _ _)).
Qed.



Equations run_bforest {A : Type} {n : nat}
  (x : @btree 1) (xs : @bforest A (num_leaves x) n) : @btree A :=
run_bforest x (@exist _ _ xss pf) :=
  join_btree (fmap snd (zip_btree x xss (proj1 pf))).

Lemma run_bforest_id (x : @btree 1) :
  run_bforest x (id_bforest () (num_leaves x)) = x.
rewrite id_bforest_equation_1.
rewrite run_bforest_equation_1.
pose (join_zip_btree_id_l x
  (proj1 (id_is_bforest () (num_leaves x) 0))
).
simpl in e.
exact e.
Qed.

Lemma run_bforest_trans : forall {x y z : @btree 1}
  (xs : bforest (num_leaves x) (num_leaves y))
  (pfx : run_bforest x xs = y)
  (ys : bforest (num_leaves y) (num_leaves z))
  (pfy : run_bforest y ys = z),
    run_bforest x (trans_bforest xs ys) = z.
intros.

destruct xs, ys.
rewrite trans_bforest_equation_1.
rewrite run_bforest_equation_1.
destruct i, i0.
Local Transparent join_zip_btrees.
unfold join_zip_btrees.
Local Opaque join_zip_btrees.
rewrite run_bforest_equation_1 in pfx.
rewrite run_bforest_equation_1 in pfy.
rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)).
rewrite <- (zip_btrees_err_correct _ _ _ (bnil tt)).
rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)) in pfy.
rewrite <- pfy in *.
clear pfy.
rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)) in pfx.
rewrite <- pfx in *.
clear pfx.

assert (H0 :
  list_num_leaves x0 = length x1
).
{
  exact (eq_trans (eq_sym e0) e1).
}
{
  assert (H1 :
    list_num_leaves [x] = length x0
  ).
  {
    rewrite list_num_leaves_equation_2.
    rewrite list_num_leaves_equation_1.
    rewrite <- plus_n_O.
    exact e.
  }
  {
    pose (H := @assoc_join_zip_btree_err x x1 x0 nil H0 H1).
    rewrite firstn_map in H.
    assert (e' :
      num_leaves x = length (zip_btrees_err x0 x1 (bnil ()))
    ).
    {
      rewrite e.
      rewrite (zip_btrees_err_correct _ _ (eq_trans (eq_sym e0) e1) _).
      rewrite length_zip_btrees.
      reflexivity.
    }
    {
      simpl.
      rewrite (f_equal
        (fun xx =>
              join_btree
            (fmap_btree snd
            (zip_btree_err x
              (List.map (λ x : btree, join_btree (fmap_btree snd x))
                 (firstn xx (zip_btrees_err x0 x1 (bnil ()))))
              (bnil ())))
        )
        e'
      ) in H.
      rewrite firstn_all in H.
      refine (eq_trans (eq_sym H) _).
      f_equal.
      f_equal.
      f_equal.
      {
        f_equal.
        f_equal.
        f_equal.
        rewrite e.
        rewrite firstn_all.
        reflexivity.
      }
      {
        rewrite e.
        rewrite firstn_all.
        rewrite num_leaves_join.
        rewrite leaves_fmap.
        rewrite (zip_btree_err_correct _ _ e).
        rewrite leaves_zip_btree.
        rewrite list_map_snd_combine.
        rewrite eq_num_leaves.
        rewrite e.
        rewrite firstn_all.
        rewrite (eq_trans (eq_sym e0) e1).
        rewrite firstn_all.
        reflexivity.
      }
    }
  }
}
Qed.

