Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.Prod.
Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations zip_btree {A B} (xs : @btree A) (ys : list B) (pf : num_leaves xs = length ys) : @btree (A * B) :=
zip_btree (bnil x) ys pf := bnil (pair x (dep_hd ys _)) ;
zip_btree (bcons x y) ys pf :=
  bcons
    (zip_btree
      x
      (firstn (num_leaves x) ys)
      (num_leaves_firstn pf))
    (zip_btree
      y
      (skipn  (num_leaves x) ys)
      (num_leaves_skipn pf)
    ).

(* Notation "zip_btree_eq" := (eq_zip_btree). *)
Fixpoint eq_zip_btree {A B} (xs ys : @btree A) (zs ws : list B)
  (pfx : num_leaves xs = length zs)
  (pfy : num_leaves ys = length ws)
  (eqxy : xs = ys)
  (eqzw : zs = ws) :
    zip_btree xs zs pfx = zip_btree ys ws pfy.
destruct eqxy, eqzw, xs.

destruct zs.

discriminate.

reflexivity.

repeat (rewrite zip_btree_equation_2).
refine (bcons_eq _ _).

exact (eq_zip_btree _ _ _ _ _ _ _ _ eq_refl eq_refl).

exact (eq_zip_btree _ _ _ _ _ _ _ _ eq_refl eq_refl).
Qed.

Fixpoint leaves_zip_btree {A B} (xs : @btree A) (ys : list B) (pf : num_leaves xs = length ys) :
  leaves (zip_btree xs ys pf) = combine (leaves xs) ys.
destruct xs.

rewrite leaves_equation_1.
destruct ys.

discriminate.

destruct ys.

rewrite zip_btree_equation_1.
reflexivity.

discriminate.

rewrite leaves_equation_2.
destruct ys.

pose (num_leaves_positive _ pf).
destruct f.

rewrite zip_btree_equation_2.
rewrite leaves_equation_2.
rewrite combine_app.
refine (list_app_eq _ _).

rewrite eq_num_leaves.
exact (leaves_zip_btree _ _ _ _ _).

rewrite eq_num_leaves.
exact (leaves_zip_btree _ _ _ _ _).
Defined.

(* TODO: Rewrite to use leaves_zip_btree *)
(* The same definition with 'fix' produces a known bug: https://github.com/coq/coq/issues/11013 *)
Fixpoint num_leaves_zip_btree {A B} (xs : @btree A) (ys : list B) (pf : num_leaves xs = length ys) :
  num_leaves (zip_btree xs ys pf) = num_leaves xs.
Proof.
destruct xs.

pose pf.
rewrite num_leaves_equation_1 in e.
destruct ys.

discriminate.

destruct ys.

rewrite num_leaves_equation_1.
rewrite zip_btree_equation_1.
rewrite num_leaves_equation_1.
reflexivity.

discriminate.

rewrite num_leaves_equation_2.
destruct ys.

pose (num_leaves_positive (bcons xs1 xs2) pf).
destruct f.

rewrite zip_btree_equation_2.
rewrite num_leaves_equation_2.
refine (nat_plus_eq _ _).

exact (num_leaves_zip_btree _ _ xs1 (firstn (num_leaves xs1) (b :: ys)) (num_leaves_firstn pf)).

exact (num_leaves_zip_btree _ _ xs2 (skipn (num_leaves xs1) (b :: ys)) (num_leaves_skipn pf)).
Defined.

Local Close Scope nat_scope.

Equations zip_btree_err {A B} (xs : @btree A) (ys : list B) : B -> @btree (A * B) :=
zip_btree_err (bnil x) nil := fun err => bnil (pair x err) ;
zip_btree_err (bnil x) (cons y _) := fun _ => bnil (pair x y) ;
zip_btree_err (bcons x y) ys := fun err =>
  bcons
    (zip_btree_err
      x
      (firstn (num_leaves x) ys)
      err
    )
    (zip_btree_err
      y
      (skipn  (num_leaves x) ys)
      err
    ).

Fixpoint zip_btree_err_correct {A B} (xs : @btree A) (ys : list B) : forall
  (pf : num_leaves xs = length ys)
  (z : B),
    zip_btree_err xs ys z = zip_btree xs ys pf.
intros.
destruct ys.
{
  destruct (num_leaves_positive xs pf).
}
{
  destruct xs.
  {
    rewrite zip_btree_err_equation_2.
    rewrite zip_btree_equation_1.
    refine (bnil_eq _).
    refine (pair_eq eq_refl _).
    rewrite dep_hd_equation_2.
    reflexivity.
  }
  {
    rewrite zip_btree_err_equation_3.
    rewrite zip_btree_equation_2.
    refine (bcons_eq _ _).
    {
      exact (zip_btree_err_correct _ _ _ _ _ _).
    }
    {
      exact (zip_btree_err_correct _ _ _ _ _ _).
    }
  }
}
Qed.

