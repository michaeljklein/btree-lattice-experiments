Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

(* Not main module *)
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.
Require Import Embed.Theory.Btree.Zip.
Require Import Embed.Theory.Btree.Lattice.

Require Import Embed.Theory.Bforest.Zip.
Require Import Embed.Theory.Bforest.Is.
Require Import Embed.Theory.Bforest.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.List.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Definition ble {A : Type} (x : @btree 1) (y : @btree A) : Type :=
  { xy : @bforest A (num_leaves x) (num_leaves y)
  | run_bforest x xy = y
  }.

Lemma eq_ble {A : Type} {eqDecA : EqDec A} (x : @btree 1) (y : @btree A)
  (xs : ble x y)
  (ys : ble x y)
  (pfx : proj1_sig xs = proj1_sig ys) :
    xs = ys.
destruct xs, ys.
refine (eq_sig
  (exist (λ xy : bforest (num_leaves x) (num_leaves y), run_bforest x xy = y) x0 e)
  (exist (λ xy : bforest (num_leaves x) (num_leaves y), run_bforest x xy = y) x1 e0)
  pfx
  _
).
simpl in *.
destruct pfx.
simpl.
exact (UIP_dec dec_eq_btree _ _).
Qed.

Equations ble_id (x : @btree 1) : ble x x :=
ble_id x :=
  @exist _ _
    (id_bforest tt (num_leaves x))
    (run_bforest_id x).

Equations trans_ble {x y z : @btree 1} (xy : ble x y) (yz : ble y z) : ble x z :=
trans_ble (@exist _ _ xs pfx) (@exist _ _ ys pfy) :=
  @exist _ _ (trans_bforest xs ys) (run_bforest_trans xs pfx ys pfy).

Program Instance BextensionC : Category := {
  obj     := @btree 1 ;

  hom     := ble ;

  homset  := fun _ _ => {| equiv := eq |} ;

  id      := ble_id ;

  compose := fun _ _ _ => Basics.flip trans_ble
}.
Next Obligation.
destruct f.
rewrite ble_id_equation_1.
unfold Basics.flip.
rewrite trans_ble_equation_1.
refine (eq_ble _ _ _ _ _).
simpl.
exact (id_left _).
Qed.

Next Obligation.
destruct f.
rewrite ble_id_equation_1.
unfold Basics.flip.
rewrite trans_ble_equation_1.
refine (eq_ble _ _ _ _ _).
simpl.
exact (id_right _).
Qed.

Next Obligation.
destruct f, g, h.
unfold Basics.flip.
repeat (rewrite trans_ble_equation_1).
refine (eq_ble _ _ _ _ _).
simpl.
exact (comp_assoc _ _ _).
Qed.

Next Obligation.
destruct f, g, h.
unfold Basics.flip.
repeat (rewrite trans_ble_equation_1).
refine (eq_ble _ _ _ _ _).
simpl.
exact (comp_assoc_sym _ _ _).
Qed.

(* This is an isomorphism, since ble is Affine *)
(* See Embed.Theory.Btree.Segment.Affine for an (incomplete) proof *)
Lemma ble_cons (x y z w : @btree 1) :
  ble (bcons x y) (bcons z w) ↔ ble x z * ble y w.
split.
{
  intro.
  destruct H.
  destruct x0.
  rewrite run_bforest_equation_1 in e.
  rewrite zip_btree_equation_2 in e.
  rewrite fmap_btree_equation_2 in e.
  rewrite join_btree_equation_2 in e.
  inversion e.
  destruct i.
  rewrite H1.

  assert (H : list_num_leaves [x; y] = length x0).
  {
    do 2 (rewrite list_num_leaves_equation_2).
    rewrite list_num_leaves_equation_1.
    rewrite <- plus_n_O.
    rewrite <- e0.
    rewrite num_leaves_equation_2.
    reflexivity.
  }
  split.
  {
    assert (xz :
      is_bforest (num_leaves x) (num_leaves z) (firstn (num_leaves x) x0)
    ).
    {
      split.
      {
        exact (list_num_leaves_firstn H).
      }
      {
        rewrite <- H0.
        rewrite num_leaves_join.
        rewrite leaves_fmap.
        rewrite leaves_zip_btree.
        rewrite list_map_snd_combine.
        rewrite eq_num_leaves.
        rewrite firstn_firstn.
        rewrite PeanoNat.Nat.min_id.
        reflexivity.
      }
    }
    {
      refine (@exist _ _ (@exist _ _ (firstn (num_leaves x) x0) xz) _).
      rewrite run_bforest_equation_1.
      rewrite <- H0.
      do 2 (rewrite <- (zip_btree_err_correct _ _ _ (bnil tt))).
      reflexivity.
    }
  }
  {
    (* Same proof, but H0 -> H1, firstn -> skipn *)
    assert (yw :
      is_bforest (num_leaves y) (num_leaves w) (skipn (num_leaves x) x0)
    ).
    {
      split.
      {
        rewrite <- (list_num_leaves_skipn H).
        rewrite list_num_leaves_equation_2.
        rewrite list_num_leaves_equation_1.
        rewrite <- plus_n_O.
        reflexivity.
      }
      {
        (* Almost the same proof as above *)
        rewrite <- H1.
        rewrite num_leaves_join.
        rewrite leaves_fmap.
        rewrite leaves_zip_btree.
        rewrite list_map_snd_combine.
        rewrite eq_num_leaves.
        rewrite firstn_skipn_comm.
        rewrite <- num_leaves_equation_2.
        refine (eq_trans (f_equal
          (fun xx =>
            list_num_leaves (skipn (num_leaves x) (firstn xx x0))
          )
          e0
        ) _).
        rewrite firstn_all.
        reflexivity.
      }
    }
    {
      refine (@exist _ _ (@exist _ _ (skipn (num_leaves x) x0) yw) _).
      rewrite run_bforest_equation_1.
      rewrite <- H1.
      do 2 (rewrite <- (zip_btree_err_correct _ _ _ (bnil tt))).
      reflexivity.
    }
  }
}

{
  intro.
  destruct H.
  destruct b, b0.
  destruct x0, x1.
  destruct i, i0.
  rewrite run_bforest_equation_1 in e, e0.
  assert (xy :
    is_bforest (num_leaves (bcons x y)) (num_leaves (bcons z w)) (x0 ++ x1)
  ).
  {
    split.
    {
      rewrite num_leaves_equation_2.
      rewrite app_length.
      rewrite (nat_plus_eq e1 e3).
      reflexivity.
    }
    {
      (* Almost the same proof as above *)
      rewrite num_leaves_equation_2.
      rewrite <- list_num_leaves_app.
      rewrite (nat_plus_eq e2 e4).
      reflexivity.
    }
  }
  {
    refine (@exist _ _ (@exist _ _ (x0 ++ x1) xy) _).
    rewrite run_bforest_equation_1.
    rewrite zip_btree_equation_2.
    rewrite fmap_btree_equation_2.
    rewrite join_btree_equation_2.
    refine (bcons_eq _ _).
    {
      rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)).
      rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)) in e.
      rewrite (firstn_app (num_leaves x) x0 x1).
      rewrite e1.
      rewrite firstn_all.
      rewrite PeanoNat.Nat.sub_diag.
      simpl.
      rewrite app_nil_r.
      exact e.
    }
    {
      (* The same proof, with e -> e0 and firstn -> skipn *)
      rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)).
      rewrite <- (zip_btree_err_correct _ _ _ (bnil tt)) in e0.
      rewrite (skipn_app (num_leaves x) x0 x1).
      rewrite e1.
      rewrite skipn_all.
      rewrite PeanoNat.Nat.sub_diag.
      simpl.
      exact e0.
    }
  }
}
Qed.

Fixpoint ble_nil (x : @btree 1) : ble (bnil tt) x.
assert (xs :
  is_bforest (num_leaves (bnil ())) (num_leaves x) [x]
).
{
  rewrite num_leaves_equation_1.
  split.
  {
    reflexivity.
  }
  {
    rewrite list_num_leaves_equation_2.
    rewrite list_num_leaves_equation_1.
    rewrite <- plus_n_O.
    reflexivity.
  }
}
{
  refine (@exist _ _ (@exist _ _ (cons x nil) xs) _).
  destruct xs.
  rewrite run_bforest_equation_1.
  rewrite zip_btree_equation_1.
  rewrite fmap_btree_equation_1.
  rewrite join_btree_equation_1.
  simpl.
  rewrite dep_hd_equation_2.
  reflexivity.
}
Qed.

Fixpoint ble_consistent (x y : @btree 1) :
  ble x y ↔ and_btree x y = x.
split.
{
  intro.
  destruct x, y.
  {
    destruct t.
    reflexivity.
  }
  {
    destruct t.
    reflexivity.
  }
  {
    simpl.
    destruct H.
    destruct x.
    destruct i.
    rewrite run_bforest_equation_1 in e.
    rewrite zip_btree_equation_2 in e.
    rewrite fmap_btree_equation_2 in e.
    rewrite join_btree_equation_2 in e.
    discriminate.
  }
  {
    simpl.
    destruct (fst (ble_cons _ _ _ _) H).
    refine (bcons_eq _ _).
    {
      exact (fst (ble_consistent x1 y1) b).
    }
    {
      exact (fst (ble_consistent x2 y2) b0).
    }
  }
}
{
  intro.
  destruct x, y.
  {
    destruct t.
    exact (ble_nil _).
  }
  {
    exact (ble_nil _).
  }
  {
    discriminate.
  }
  {
    refine (snd (ble_cons _ _ _ _) _).
    rewrite and_btree_equation_4 in H.
    inversion H.
    rewrite H1, H2.
    split.
    {
      exact (snd (ble_consistent x1 y1) H1).
    }
    {
      exact (snd (ble_consistent x2 y2) H2).
    }
  }
}
Qed.

