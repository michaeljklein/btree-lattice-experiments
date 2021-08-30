Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.List.
Require Import Embed.Theory.Datatypes.List.Zip.
Require Import Embed.Theory.Datatypes.Prod.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.
Require Import Embed.Theory.Btree.Leaves.
Require Import Embed.Theory.Btree.Zip.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations zip_btrees {A B} (xs : list (@btree A)) (ys : list B) (pf : list_num_leaves xs = length ys) : list (@btree (A * B)) :=
zip_btrees nil _ _ := nil ;
zip_btrees (cons z zs) ws pf :=
  cons
    (zip_btree
      z
      (firstn (num_leaves z) ws)
      (list_num_leaves_firstn pf)
    )
    (zip_btrees
      zs
      (skipn  (num_leaves z) ws)
      (list_num_leaves_skipn pf)
    ).

Notation list_eq_cons := list_cons_eq.

Fixpoint eq_zip_btrees {A B} (xs ys : list (@btree A)) (zs ws : list B)
  (pfx : list_num_leaves xs = length zs)
  (pfy : list_num_leaves ys = length ws)
  (eqxy : xs = ys)
  (eqzw : zs = ws) :
    zip_btrees xs zs pfx = zip_btrees ys ws pfy.
destruct eqxy, eqzw, xs.

reflexivity.

rewrite zip_btrees_equation_2.
refine (list_cons_eq _ _).

exact (eq_zip_btree _ _ _ _ _ _ eq_refl eq_refl).

exact (eq_zip_btrees _ _ _ _ _ _ _ _ eq_refl eq_refl).
Qed.

Fixpoint length_zip_btrees {A B} (xs : list (@btree A)) (ys : list B)
  (pf : list_num_leaves xs = length ys) :
    length (zip_btrees xs ys pf) = length xs.
destruct xs.

rewrite zip_btrees_equation_1.
reflexivity.

rewrite zip_btrees_equation_2.
refine (length_cons_eq _).
exact (length_zip_btrees _ _ xs (skipn (num_leaves b) ys) (list_num_leaves_skipn pf)).
Defined.

Fixpoint list_num_leaves_zip_btrees {A B} (xs : list (@btree A)) (ys : list B)
  (pf : list_num_leaves xs = length ys) :
    list_num_leaves (zip_btrees xs ys pf) = list_num_leaves xs.
destruct xs.

rewrite zip_btrees_equation_1.
reflexivity.

rewrite zip_btrees_equation_2.
repeat (rewrite list_num_leaves_equation_2).
refine (nat_plus_eq _ _).

exact (num_leaves_zip_btree _ _ _).

exact (list_num_leaves_zip_btrees _ _ xs (skipn (num_leaves b) ys) (list_num_leaves_skipn pf)).
Defined.

Equations join_zip_btrees {A B} (xs : list (@btree A)) (ys : list (@btree B)) (pf : list_num_leaves xs = length ys) :
  list (@btree B) :=
join_zip_btrees xs ys pf := List.map (Basics.compose join_btree (fmap_btree snd)) (zip_btrees xs ys pf).

Lemma length_join_zip_btrees {A B} (xs : list (@btree A)) (ys : list (@btree B)) (pf : list_num_leaves xs = length ys) :
  length (join_zip_btrees xs ys pf) = length xs.
rewrite join_zip_btrees_equation_1.
exact (eq_trans (map_length (join_btree \o fmap_btree snd) (zip_btrees xs ys pf)) (length_zip_btrees xs ys pf)).
Defined.

Fixpoint list_num_leaves_join_zip_btrees {A B} (xs : list (@btree A)) (ys : list (@btree B))
  (pf : list_num_leaves xs = length ys) :
    list_num_leaves (join_zip_btrees xs ys pf) = list_num_leaves ys.
rewrite join_zip_btrees_equation_1.
destruct xs.

rewrite zip_btrees_equation_1.
unfold List.map.
destruct ys.

reflexivity.

discriminate.

rewrite zip_btrees_equation_2.
rewrite list_map_cons.
rewrite list_num_leaves_equation_2.

pose (list_num_leaves_firstn pf).
pose (list_num_leaves_skipn pf).

unfold "\o".
rewrite num_leaves_join.
rewrite leaves_fmap.
rewrite leaves_zip_btree.
rewrite list_map_snd_combine.
rewrite eq_num_leaves.
rewrite firstn_firstn.
replace (Nat.min (num_leaves b) (num_leaves b)) with
        (num_leaves b) by (exact (eq_sym (PeanoNat.Nat.min_id (num_leaves b)))).

rewrite <- join_zip_btrees_equation_1.
rewrite list_num_leaves_join_zip_btrees.
rewrite list_num_leaves_app.
rewrite firstn_skipn.
reflexivity.
Defined.

Lemma join_zip_btrees_id_l_helper {b : @btree 1} {xs : list (@btree 1)} : forall
  (pf : (num_leaves b + list_num_leaves xs)%nat =
    length (List.map (λ _ : nat, bnil ()) (seq 0 (num_leaves b + list_num_leaves xs)))
  ),
   list_num_leaves xs =
        length (List.map (λ _ : nat, bnil ()) (seq 0 (list_num_leaves xs))).
intro.
rewrite map_length in *.
rewrite seq_length in *.
auto.
Qed.

Fixpoint join_zip_btree_id_l (xs : @btree 1)
  (pf : num_leaves xs = length (List.map (fun _ : nat => bnil tt) (seq 0 (num_leaves xs)))) :
    (join_btree \o fmap_btree snd)
      (zip_btree xs (List.map (fun _ : nat => bnil tt) (seq 0 (num_leaves xs))) pf) = xs.
destruct xs.
{
  simpl.
  rewrite zip_btree_equation_1.
  rewrite fmap_btree_equation_1.
  rewrite join_btree_equation_1.
  Local Transparent list_num_leaves.
  simpl.
  Local Opaque list_num_leaves.
  rewrite dep_hd_equation_2.
  destruct t.
  reflexivity.
}
{
  rewrite zip_btree_equation_2.
  simpl.
  rewrite fmap_btree_equation_2.
  rewrite join_btree_equation_2.
  refine (bcons_eq _ _).
  {
    assert (xs1_eq : num_leaves xs1 =
      length (List.map (λ _ : nat, bnil ()) (seq 0 (num_leaves xs1)))
    ).
    {
      rewrite map_length.
      rewrite seq_length.
      reflexivity.
    }
    {
      pose (H := join_zip_btree_id_l xs1 xs1_eq).
      simpl in H.
      inversion H.
      refine (eq_trans _ H0).
      do 2 (refine (f_equal _ _)).
      refine (eq_zip_btree _ _ _ _ _ _ eq_refl _).
      rewrite firstn_map.
      refine (f_equal _ _).
      rewrite firstn_seq.
      refine (f_equal _ _).
      assert (H_min : Nat.min (num_leaves xs1) (num_leaves xs1 + num_leaves xs2) = num_leaves xs1).
      {
        replace (Nat.min (num_leaves xs1)) with
                (Nat.min (num_leaves xs1 + 0%nat)) by
                (refine (f_equal _ _); rewrite plus_n_O; reflexivity).
        rewrite PeanoNat.Nat.add_min_distr_l.
        rewrite PeanoNat.Nat.min_0_l.
        rewrite plus_n_O.
        reflexivity.
      }
      exact H_min.
    }
  }
  {
    assert (xs2_eq : num_leaves xs2 =
      length (List.map (λ _ : nat, bnil ()) (seq 0 (num_leaves xs2)))
    ).
    {
      rewrite map_length.
      rewrite seq_length.
      reflexivity.
    }
    {
      pose (H := join_zip_btree_id_l xs2 xs2_eq).
      simpl in H.
      inversion H.
      refine (eq_trans _ H0).
      do 2 (refine (f_equal _ _)).
      refine (eq_zip_btree _ _ _ _ _ _ eq_refl _).
      rewrite skipn_map.
      rewrite skipn_seq.
      assert (cancel_plus_minus :
        (num_leaves xs1 + num_leaves xs2 - num_leaves xs1)%nat =
        num_leaves xs2
      ).
      {
        rewrite Minus.minus_plus.
        reflexivity.
      }
      {
        refine (eq_trans (list_map_const_seq _ _ 0%nat _) _).
        do 2 (refine (f_equal _ _)).
        exact cancel_plus_minus.
      }
    }
  }
}
Qed.

Fixpoint join_zip_btrees_id_l {xs : list (@btree 1)} : forall
  (pf : list_num_leaves xs = length (List.map (λ _ : nat, bnil ()) (seq 0 (list_num_leaves xs)))),
    join_zip_btrees
      xs
      (List.map (λ _ : nat, bnil ()) (seq 0 (list_num_leaves xs)))
      pf = xs.
intros.
rewrite join_zip_btrees_equation_1.
destruct xs.
{
  Local Transparent list_num_leaves.
  simpl in pf.
  simpl.
  Local Opaque list_num_leaves.
  rewrite zip_btrees_equation_1.
  reflexivity.
}
{
  Local Transparent list_num_leaves.
  simpl in pf.
  Local Opaque list_num_leaves.
  refine (eq_trans _ (f_equal (cons b) (join_zip_btrees_id_l xs (join_zip_btrees_id_l_helper pf)))).
  clear join_zip_btrees_id_l.
  rewrite zip_btrees_equation_2.
  destruct b.
  {
    simpl.
    assert (H : join_btree
      (fmap_btree snd
         (zip_btree (bnil t)
            match
              List.map (λ _ : nat, bnil ())
                (seq 0 (list_num_leaves (bnil t :: xs)))
            with
            | [] => []
            | a :: _ => [a]
            end (list_num_leaves_firstn pf))) = bnil t).
    {
      rewrite zip_btree_equation_1.
      rewrite fmap_btree_equation_1.
      rewrite join_btree_equation_1.
      Local Transparent list_num_leaves.
      simpl.
      Local Opaque list_num_leaves.
      rewrite dep_hd_equation_2.
      destruct t.
      reflexivity.
    }
    {
      refine (list_cons_eq H _).
      refine (f_equal _ _).
      refine (eq_zip_btrees _ _ _ _ _ _ eq_refl _).
      exact (list_map_const_seq _ _ _ _).
    }
  }
  {
    rewrite zip_btree_equation_2.
    simpl.
    rewrite fmap_btree_equation_2.
    rewrite join_btree_equation_2.
    refine (list_cons_eq _ _).
    {
      refine (bcons_eq _ _).
      {
        assert (b1_eq : num_leaves b1 =
          length (List.map (λ _ : nat, bnil ()) (seq 0 (num_leaves b1)))
        ).
        {
          rewrite map_length.
          rewrite seq_length.
          reflexivity.
        }
        {
          pose (H := join_zip_btree_id_l b1 b1_eq).
          simpl in H.
          inversion H.
          refine (eq_trans _ H0).
          do 2 (refine (f_equal _ _)).
          refine (eq_zip_btree _ _ _ _ _ _ eq_refl _).
          rewrite firstn_firstn.
          assert (H_min : Nat.min (num_leaves b1) (num_leaves b1 + num_leaves b2) = num_leaves b1).
          {
            replace (Nat.min (num_leaves b1)) with
                    (Nat.min (num_leaves b1 + 0%nat)) by
                    (refine (f_equal _ _); rewrite plus_n_O; reflexivity).
            rewrite PeanoNat.Nat.add_min_distr_l.
            rewrite PeanoNat.Nat.min_0_l.
            rewrite plus_n_O.
            reflexivity.
          }
          {
            (* For some reason, (rewrite H_min) doesn't work. *)
            refine (eq_trans (f_equal (fun n => 
              firstn n
              (List.map (λ _ : nat, bnil ())
              (seq 0 (list_num_leaves (bcons b1 b2 :: xs))))
              ) H_min) _).
            repeat (rewrite firstn_map).
            refine (f_equal _ _).
            repeat (rewrite firstn_seq).
            refine (f_equal _ _).
            repeat (rewrite list_num_leaves_equation_2).
            rewrite num_leaves_equation_2.
            rewrite <- PeanoNat.Nat.add_assoc.
            replace (Nat.min (num_leaves b1)) with
                    (Nat.min (num_leaves b1 + 0)) by
                    (rewrite <- plus_n_O; reflexivity).
            rewrite PeanoNat.Nat.add_min_distr_l.
            rewrite PeanoNat.Nat.min_0_l.
            rewrite <- plus_n_O.
            reflexivity.
          }
        }
      }
      {
        assert (b2_eq : num_leaves b2 =
          length (List.map (λ _ : nat, bnil ()) (seq 0 (num_leaves b2)))
        ).
        {
          rewrite map_length.
          rewrite seq_length.
          reflexivity.
        }
        {
          pose (H := join_zip_btree_id_l b2 b2_eq).
          simpl in H.
          inversion H.
          refine (eq_trans _ H0).
          do 2 (refine (f_equal _ _)).
          refine (eq_zip_btree _ _ _ _ _ _ eq_refl _).
          rewrite <- firstn_skipn_comm.
          rewrite skipn_map.
          rewrite skipn_seq.
          repeat (rewrite firstn_map).
          repeat (rewrite firstn_seq).
          rewrite <- plus_n_O.
          refine (eq_trans (list_map_const_seq _ _ O _) _).
          do 2 (refine (f_equal _ _)).
          repeat (rewrite list_num_leaves_equation_2).
          rewrite num_leaves_equation_2.
          assert (cancel_sub_num_leaves :
            (num_leaves b1 + num_leaves b2 + list_num_leaves xs - num_leaves b1)%nat =
            (num_leaves b2 + list_num_leaves xs)%nat).
          {
            rewrite <- PeanoNat.Nat.add_assoc.
            rewrite Minus.minus_plus.
            reflexivity.
          }
          {
            rewrite <- PeanoNat.Nat.add_assoc.
            rewrite Minus.minus_plus.
            refine (eq_trans (f_equal
              (fun x => Nat.min x (num_leaves b2 + list_num_leaves xs))
              (plus_n_O (num_leaves b2))
            ) _).
            rewrite PeanoNat.Nat.add_min_distr_l.
            rewrite PeanoNat.Nat.min_0_l.
            rewrite <- plus_n_O.
            reflexivity.
          }
        }
      }
    }
    {
      rewrite join_zip_btrees_equation_1.
      refine (f_equal _ _).
      refine (eq_zip_btrees _ _ _ _ _ _ eq_refl _).
      rewrite skipn_map.
      rewrite skipn_seq.
      assert (cancel_plus_minus :
        (num_leaves (bcons b1 b2) + list_num_leaves xs - (num_leaves b1 + num_leaves b2))%nat =
        (list_num_leaves xs)
      ).
      {
        rewrite num_leaves_equation_2.
        rewrite Minus.minus_plus.
        reflexivity.
      }
      {
        refine (eq_trans (list_map_const_seq _ _ 0%nat _) _).
        do 2 (refine (f_equal _ _)).
        exact cancel_plus_minus.
      }
    }
  }
}
Qed.

(* Similar to join_zip_btrees_id_l, but significantly shorter *)
Fixpoint join_zip_btrees_id_r {xs : list (@btree 1)} : forall
  (pf : list_num_leaves (List.map (λ _ : nat, bnil ()) (seq 0 (length xs))) = length xs),
    join_zip_btrees
      (List.map (λ _ : nat, bnil ()) (seq 0 (length xs)))
      xs
      pf = xs.
intros.
rewrite join_zip_btrees_equation_1.
destruct xs.
{
  Local Transparent list_num_leaves.
  simpl in pf.
  simpl.
  Local Opaque list_num_leaves.
  rewrite zip_btrees_equation_1.
  reflexivity.
}
{
  Local Transparent list_num_leaves.
  simpl in pf.
  Local Opaque list_num_leaves.
  pose (pf' := eq_add_S _ _ pf).
  pose (pf'' := eq_trans (f_equal list_num_leaves (list_map_const_seq (bnil tt) 0%nat 1%nat (length xs))) pf').
  refine (eq_trans _ (f_equal (cons b) (join_zip_btrees_id_r xs pf''))).
  clear join_zip_btrees_id_r.
  simpl.
  rewrite zip_btrees_equation_2.
  destruct b.
  {
    simpl.
    refine (list_cons_eq _ _).
    {
      rewrite zip_btree_equation_1.
      rewrite fmap_btree_equation_1.
      rewrite join_btree_equation_1.
      simpl.
      rewrite dep_hd_equation_2.
      reflexivity.
    }
    {
      refine (f_equal _ _).
      refine (eq_zip_btrees _ _ _ _ _ _ _ eq_refl).
      exact (list_map_const_seq _ _ _ _).
    }
  }
  {
    simpl.
    rewrite zip_btree_equation_1.
    rewrite fmap_btree_equation_1.
    rewrite join_btree_equation_1.
    simpl.
    refine (list_cons_eq _ _).
    {
      rewrite dep_hd_equation_2.
      reflexivity.
    }
    {
      rewrite join_zip_btrees_equation_1.
      refine (f_equal _ _).
      refine (eq_zip_btrees _ _ _ _ _ _ _ eq_refl).
      exact (list_map_const_seq _ _ _ _).
    }
  }
}
Qed.



Equations zip_btrees_err {A B} (xs : list (@btree A)) (ys : list B)
  (err : B) :
  list (@btree (A * B)) :=
zip_btrees_err nil _ := fun _ => nil ;
zip_btrees_err (cons z zs) ws := fun err =>
  cons
    (zip_btree_err
      z
      (firstn (num_leaves z) ws)
      err
    )
    (zip_btrees_err
      zs
      (skipn  (num_leaves z) ws)
      err
    ).

Fixpoint zip_btrees_err_correct {A B} (xs : list (@btree A)) (ys : list B) : forall
  (pf : list_num_leaves xs = length ys)
  (err : B),
    zip_btrees_err xs ys err = zip_btrees xs ys pf.
intros.
destruct xs.
{
  rewrite zip_btrees_err_equation_1.
  rewrite zip_btrees_equation_1.
  reflexivity.
}
{
  rewrite zip_btrees_err_equation_2.
  rewrite zip_btrees_equation_2.
  refine (list_cons_eq _ _).
  {
    exact (zip_btree_err_correct _ _ _ _).
  }
  {
    exact (zip_btrees_err_correct _ _ _ _ _ _).
  }
}
Qed.


Fixpoint zip_combine_zip_btree {A B} (xs : list (@btree A)) (ys : list B)
  (pf : total (map num_leaves xs) = length ys)
  (pf' : list_num_leaves xs = length ys) :
  zip_combine num_leaves zip_btree xs ys pf = zip_btrees xs ys pf'.
destruct xs.
{
  rewrite zip_btrees_equation_1.
  rewrite zip_combine_equation_1.
  reflexivity.
}
{
  rewrite zip_btrees_equation_2.
  rewrite zip_combine_equation_2.
  refine (list_cons_eq _ _).
  {
    exact (eq_zip_btree _ _ _ _ _ _ eq_refl eq_refl).
  }
  {
    exact (zip_combine_zip_btree _ _ _ _ _ _).
  }
}
Qed.

(* Almost the same proof as for zip_combine_zip_btree *)
Fixpoint zip_combine_err_zip_btree_err {A B} (xs : list (@btree A)) (ys : list B) : forall
  (pf : total (map num_leaves xs) = length ys)
  (pf' : list_num_leaves xs = length ys) (err : B),
  zip_combine_err num_leaves zip_btree_err xs ys err = zip_btrees_err xs ys err.
intros.
destruct xs.
{
  rewrite zip_btrees_err_equation_1.
  rewrite zip_combine_err_equation_1.
  reflexivity.
}
{
  rewrite zip_btrees_err_equation_2.
  rewrite zip_combine_err_equation_2.
  refine (list_cons_eq _ _).
  {
    reflexivity.
  }
  {
    refine (zip_combine_err_zip_btree_err _ _ _ _ _ _ _).
    {
      rewrite <- list_num_leaves_total.
      exact (list_num_leaves_skipn pf').
    }
    {
      exact (list_num_leaves_skipn pf').
    }
  }
}
Qed.



Fixpoint assoc_join_zip_btree_err {b : @btree 1} {xs ys zs : list (@btree 1)}
  (pfxy : list_num_leaves ys = length xs)
  (pfyz : list_num_leaves (b :: zs) = length ys) :
    join_btree
      (fmap_btree snd
         (zip_btree_err
            (join_btree
               (fmap_btree snd
                  (zip_btree_err b (firstn (num_leaves b) ys) (bnil ()))))
            (firstn
               (num_leaves
                  (join_btree
                     (fmap_btree snd
                        (zip_btree_err b (firstn (num_leaves b) ys) (bnil ())))))
               xs) (bnil ()))) =
    join_btree
      (fmap_btree snd
         (zip_btree_err b
            (firstn (num_leaves b)
               (List.map (λ x : btree, join_btree (fmap_btree snd x))
                  (zip_btrees_err ys xs (bnil ())))) (bnil ()))).
destruct ys.
{
  rewrite list_num_leaves_equation_2 in pfyz.
  destruct (proj1 (PeanoNat.Nat.eq_add_0 _ _) pfyz).
  destruct (num_leaves_positive _ H).
}
{
  destruct xs.
  {
    rewrite list_num_leaves_equation_2 in pfxy.
    destruct (proj1 (PeanoNat.Nat.eq_add_0 _ _) pfxy).
    destruct (num_leaves_positive _ H).
  }
  {
    destruct b.
    {
      clear assoc_join_zip_btree_err.
      rewrite zip_btrees_err_equation_2 in *.
      rewrite num_leaves_equation_1 in *.
      simpl in *.
      do 2 (rewrite zip_btree_err_equation_2).
      do 2 (rewrite fmap_btree_equation_1).
      do 2 (rewrite join_btree_equation_1).
      simpl.
      reflexivity.
    }
    {
      assert (H :
        num_leaves b2 = length (firstn (num_leaves b2) (b0 :: ys))
      ).
      {
        rewrite list_num_leaves_equation_2 in pfyz.
        rewrite num_leaves_equation_2 in pfyz.
        rewrite <- PeanoNat.Nat.add_assoc in pfyz.
        do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
        exact (list_num_leaves_firstn pfyz).
      }
      {
        rewrite zip_btrees_err_equation_2 in *.
        do 2 (rewrite zip_btree_err_equation_3 in *).
        do 2 (rewrite fmap_btree_equation_2).
        do 2 (rewrite join_btree_equation_2).
        rewrite zip_btree_err_equation_3.
        rewrite fmap_btree_equation_2.
        rewrite join_btree_equation_2.
        refine (bcons_eq _ _).
        {
          do 2 (rewrite firstn_firstn).
          do 2 (rewrite num_leaves_equation_2).
          rewrite firstn_firstn.
          do 2 (rewrite nat_min_plus).
          refine (assoc_join_zip_btree_err _ _ _ (b3 :: zs) pfxy _).
          rewrite <- pfyz.
          do 3 (rewrite list_num_leaves_equation_2).
          rewrite num_leaves_equation_2.
          rewrite PeanoNat.Nat.add_assoc.
          reflexivity.
        }
        {
          do 2 (rewrite num_leaves_equation_2).
          rewrite firstn_firstn.
          rewrite nat_min_plus.
          do 3 (rewrite <- firstn_skipn_comm).
          refine (eq_trans (assoc_join_zip_btree_err
            b3
            (skipn
              (num_leaves (join_btree (fmap_btree snd (zip_btree_err b2 (firstn (num_leaves b2) (b0 :: ys)) (bnil ())))))
              (b1 :: xs)
            )
            (skipn (num_leaves b2) (b0 :: ys))
            (zs)
            _ _
          ) _).
          {
            clear assoc_join_zip_btree_err.
            rewrite list_num_leaves_equation_2 in pfyz.
            rewrite num_leaves_equation_2 in pfyz.
            rewrite <- PeanoNat.Nat.add_assoc in pfyz.
            do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
            rewrite (list_num_leaves_firstn pfyz).
            rewrite skipn_length.
            rewrite firstn_length.
            rewrite <- pfxy.
            clear pfxy.
            rewrite <- pfyz.
            rewrite list_num_leaves_equation_2.
            rewrite nat_min_plus.
            rewrite num_leaves_join.
            rewrite leaves_fmap.
            rewrite (zip_btree_err_correct _ _ H).
            rewrite leaves_zip_btree.
            rewrite list_map_snd_combine.
            rewrite firstn_firstn.
            rewrite eq_num_leaves.
            rewrite PeanoNat.Nat.min_id.
            do 2 (rewrite list_num_leaves_total).
            rewrite <- (f_equal
              (fun x => total (map[Coq.listF] num_leaves x))
              (firstn_skipn (num_leaves b2) (b0 :: ys))
            ).
            rewrite map_app.
            rewrite total_app.
            rewrite list_num_leaves_total.
            rewrite Minus.minus_plus.
            reflexivity.
          }
          {
            clear assoc_join_zip_btree_err.
            refine (list_num_leaves_skipn _).
            refine (eq_trans _ pfyz).
            repeat (rewrite list_num_leaves_equation_2).
            repeat (rewrite num_leaves_equation_2).
            rewrite PeanoNat.Nat.add_assoc.
            reflexivity.
          }
          {
            clear assoc_join_zip_btree_err.
            do 2 (f_equal).
            refine (eq_trans (zip_btree_err_correct _ _ _ _) _).
            refine (eq_trans _(eq_sym (zip_btree_err_correct _ _ _ _))).
            refine (eq_zip_btree _ _ _ _ _ _ eq_refl _).
            rewrite skipn_map.
            do 2 (rewrite firstn_map).
            f_equal.
            rewrite <- (equal_f (@zip_btrees_err_equation_2 _ _ b0 ys (b1 :: xs)) (bnil tt)).
            repeat (rewrite <- zip_combine_err_zip_btree_err).
            {
              rewrite firstn_zip_combine_err.
              {
                rewrite skipn_zip_combine_err.
                {
                  rewrite firstn_zip_combine_err.
                  {
                    refine (f_equal
                      (fun x =>
                        zip_combine_err num_leaves zip_btree_err
                        (firstn (num_leaves b3) (skipn (num_leaves b2) (b0 :: ys)))
                        x
                        (bnil ())
                      )
                      _
                    ).
                    do 2 f_equal.
                    rewrite num_leaves_join.
                    rewrite list_num_leaves_total.
                    rewrite leaves_fmap.
                    rewrite (zip_btree_err_correct _ _ H).
                    rewrite leaves_zip_btree.
                    rewrite list_map_snd_combine.
                    rewrite firstn_firstn.
                    rewrite eq_num_leaves.
                    rewrite PeanoNat.Nat.min_id.
                    reflexivity.
                  }
                  {
                    rewrite skipn_length.
                    rewrite <- pfxy.
                    rewrite list_num_leaves_total.
                    rewrite <- (f_equal
                      (fun x => total (map[Coq.listF] num_leaves x))
                      (firstn_skipn (num_leaves b2) (b0 :: ys))
                    ).
                    rewrite map_app.
                    rewrite total_app.
                    rewrite Minus.minus_plus.
                    reflexivity.
                  }
                }
                {
                  rewrite <- list_num_leaves_total.
                  exact pfxy.
                }
              }
              {
                rewrite list_num_leaves_equation_2 in pfyz.
                rewrite num_leaves_equation_2 in pfyz.
                rewrite <- PeanoNat.Nat.add_assoc in pfyz.
                do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
                rewrite (list_num_leaves_firstn pfyz).
                rewrite skipn_length.
                rewrite firstn_length.
                rewrite <- pfxy.
                clear pfxy.
                rewrite <- pfyz.
                rewrite list_num_leaves_equation_2.
                rewrite nat_min_plus.
                rewrite num_leaves_join.
                rewrite leaves_fmap.
                rewrite (zip_btree_err_correct _ _ H).
                rewrite leaves_zip_btree.
                rewrite list_map_snd_combine.
                rewrite firstn_firstn.
                rewrite eq_num_leaves.
                rewrite PeanoNat.Nat.min_id.
                do 2 (rewrite list_num_leaves_total).
                rewrite <- (f_equal
                  (fun x => total (map[Coq.listF] num_leaves x))
                  (firstn_skipn (num_leaves b2) (b0 :: ys))
                ).
                rewrite map_app.
                rewrite total_app.
                rewrite Minus.minus_plus.
                reflexivity.
              }
            }
            {
              rewrite <- list_num_leaves_total.
              exact pfxy.
            }
            {
              exact pfxy.
            }
            {
              (* Exactly the same proof as above *)
              rewrite list_num_leaves_equation_2 in pfyz.
              rewrite num_leaves_equation_2 in pfyz.
              rewrite <- PeanoNat.Nat.add_assoc in pfyz.
              do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
              rewrite (list_num_leaves_firstn pfyz).
              rewrite skipn_length.
              rewrite firstn_length.
              rewrite <- pfxy.
              clear pfxy.
              rewrite <- pfyz.
              rewrite list_num_leaves_equation_2.
              rewrite nat_min_plus.
              rewrite num_leaves_join.
              rewrite leaves_fmap.
              rewrite (zip_btree_err_correct _ _ H).
              rewrite leaves_zip_btree.
              rewrite list_map_snd_combine.
              rewrite firstn_firstn.
              rewrite eq_num_leaves.
              rewrite PeanoNat.Nat.min_id.
              do 2 (rewrite list_num_leaves_total).
              rewrite <- (f_equal
                (fun x => total (map[Coq.listF] num_leaves x))
                (firstn_skipn (num_leaves b2) (b0 :: ys))
              ).
              rewrite map_app.
              rewrite total_app.
              rewrite Minus.minus_plus.
              reflexivity.
            }
            {
              (* Almost exactly the same proof as above *)
              rewrite list_num_leaves_equation_2 in pfyz.
              rewrite num_leaves_equation_2 in pfyz.
              rewrite <- PeanoNat.Nat.add_assoc in pfyz.
              do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
              rewrite (list_num_leaves_firstn pfyz).
              rewrite skipn_length.
              rewrite firstn_length.
              rewrite <- pfxy.
              clear pfxy.
              rewrite <- pfyz.
              rewrite list_num_leaves_equation_2.
              rewrite nat_min_plus.
              rewrite num_leaves_join.
              rewrite leaves_fmap.
              rewrite (zip_btree_err_correct _ _ H).
              rewrite leaves_zip_btree.
              rewrite list_map_snd_combine.
              rewrite firstn_firstn.
              rewrite eq_num_leaves.
              rewrite PeanoNat.Nat.min_id.
              do 2 (rewrite list_num_leaves_total).
              rewrite <- (f_equal
                (fun x => total (map[Coq.listF] num_leaves x))
                (firstn_skipn (num_leaves b2) (b0 :: ys))
              ).
              rewrite map_app.
              rewrite total_app.
              rewrite list_num_leaves_total.
              rewrite Minus.minus_plus.
              reflexivity.
            }
          }
        }
      }
    }
  }
}
(* Not sure where these shelved goals came from? *)
Unshelve.
{
  rewrite firstn_length.
  rewrite map_length.
  assert (H' :
    list_num_leaves (skipn (num_leaves b2) (b0 :: ys)) =
    length
    (skipn
      (num_leaves
         (join_btree
            (fmap_btree snd
               (zip_btree_err b2 (firstn (num_leaves b2) (b0 :: ys))
                  (bnil ()))))) (b1 :: xs))
  ).
  {
    (* Almost exactly the same proof as above *)
    rewrite list_num_leaves_equation_2 in pfyz.
    rewrite num_leaves_equation_2 in pfyz.
    rewrite <- PeanoNat.Nat.add_assoc in pfyz.
    do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
    rewrite (list_num_leaves_firstn pfyz).
    rewrite skipn_length.
    rewrite firstn_length.
    rewrite <- pfxy.
    clear pfxy.
    rewrite <- pfyz.
    rewrite list_num_leaves_equation_2.
    rewrite nat_min_plus.
    rewrite num_leaves_join.
    rewrite leaves_fmap.
    rewrite (zip_btree_err_correct _ _ H).
    rewrite leaves_zip_btree.
    rewrite list_map_snd_combine.
    rewrite firstn_firstn.
    rewrite eq_num_leaves.
    rewrite PeanoNat.Nat.min_id.
    do 2 (rewrite list_num_leaves_total).
    rewrite <- (f_equal
      (fun x => total (map[Coq.listF] num_leaves x))
      (firstn_skipn (num_leaves b2) (b0 :: ys))
    ).
    rewrite map_app.
    rewrite total_app.
    rewrite list_num_leaves_total.
    rewrite Minus.minus_plus.
    reflexivity.
  }
  {
    rewrite (zip_btrees_err_correct _ _ H').
    rewrite length_zip_btrees.
    rewrite list_num_leaves_equation_2 in pfyz.
    rewrite num_leaves_equation_2 in pfyz.
    rewrite <- (PeanoNat.Nat.add_comm (num_leaves b3)) in pfyz.
    rewrite <- PeanoNat.Nat.add_assoc in pfyz.
    do 2 (rewrite <- list_num_leaves_equation_2 in pfyz).
    rewrite skipn_length.
    rewrite <- pfyz.
    do 2 (rewrite list_num_leaves_equation_2).
    rewrite PeanoNat.Nat.add_assoc.
    rewrite (PeanoNat.Nat.add_comm (num_leaves b3)).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite Minus.minus_plus.
    rewrite nat_min_plus.
    reflexivity.
  }
}
{
  rewrite skipn_map.
  rewrite firstn_map.
  rewrite map_length.
  rewrite firstn_length.
  rewrite skipn_length.
  rewrite <- (equal_f (@zip_btrees_err_equation_2 _ _ _ _ _) (bnil tt)).
  rewrite (zip_btrees_err_correct _ _ pfxy).
  rewrite length_zip_btrees.
  rewrite <- pfyz.
  rewrite list_num_leaves_equation_2.
  rewrite num_leaves_equation_2.
  rewrite <- PeanoNat.Nat.add_assoc.
  rewrite Minus.minus_plus.
  rewrite nat_min_plus.
  reflexivity.
}
Qed.



Fixpoint assoc_join_zip_btrees_err {xs ys zs : list (@btree 1)}
  (pfxy : list_num_leaves ys = length xs)
  (pfyz : list_num_leaves zs = length ys) :
    List.map (join_btree \o fmap_btree snd)
      (zip_btrees_err
         (List.map (join_btree \o fmap_btree snd)
            (zip_btrees_err zs ys (bnil ()))) xs (bnil ())) =
    List.map (join_btree \o fmap_btree snd)
      (zip_btrees_err zs
         (List.map (join_btree \o fmap_btree snd)
            (zip_btrees_err ys xs (bnil ()))) (bnil ())).
destruct zs.
{
  repeat (rewrite zip_btrees_err_equation_1).
  reflexivity.
}

{
  repeat (rewrite zip_btrees_err_equation_2; simpl).
  refine (list_cons_eq _ _).
  {
    exact (assoc_join_zip_btree_err pfxy pfyz).
  }
  {
    pose (pfyz' := list_num_leaves_skipn pfyz).
    unfold "\o" in assoc_join_zip_btrees_err.
    rewrite skipn_map.
    rewrite (zip_btrees_err_correct ys xs pfxy).
    assert (H :
      total (map[Coq.listF] num_leaves ys) = length xs
    ).
    {
      rewrite <- list_num_leaves_total.
      exact pfxy.
    }
    {
      rewrite <- (zip_combine_zip_btree _ _ H _).
      assert (H' :
        total (map[Coq.listF] num_leaves (skipn (num_leaves b) ys)) =
        length
        (skipn (total (map[Coq.listF] num_leaves (firstn (num_leaves b) ys))) xs)
      ).
      {
        rewrite skipn_length.
        rewrite <- pfxy.
        rewrite <- (f_equal
          list_num_leaves
          (firstn_skipn (num_leaves b) ys)
        ).
        rewrite list_num_leaves_total.
        rewrite map_app.
        rewrite total_app.
        rewrite Minus.minus_plus.
        reflexivity.
      }
      {
        refine (eq_trans _ (eq_sym (f_equal
          (fun x => List.map
            (λ x : btree, join_btree (fmap_btree snd x))
            (zip_btrees_err zs (List.map (λ x : btree, join_btree (fmap_btree snd x)) x) (bnil ()))
          )
          (skipn_zip_combine
          num_leaves
          zip_btree
          zip_btree_err
          zip_btree_err_correct
          (num_leaves b)
          _ _ H H' (bnil tt)
        )))).

        refine (eq_trans (assoc_join_zip_btrees_err _ _ _ _ _) _).
        {
          refine (list_num_leaves_skipn _).
          rewrite <- pfxy.
          rewrite <- (f_equal
            list_num_leaves
            (firstn_skipn (num_leaves b) ys)
          ).
          do 2 (rewrite list_num_leaves_total).
          rewrite map_app.
          rewrite total_app.
          simpl.
          rewrite total_equation_2.
          refine (nat_plus_eq _ eq_refl).
          rewrite num_leaves_join.
          rewrite leaves_fmap.
          assert (H2 :
            num_leaves b = length (firstn (num_leaves b) ys)
          ).
          {
            exact (list_num_leaves_firstn pfyz).
          }
          {
            rewrite (zip_btree_err_correct _ _ H2).
            rewrite leaves_zip_btree.
            rewrite list_map_snd_combine.
            rewrite eq_num_leaves.
            rewrite firstn_firstn.
            rewrite PeanoNat.Nat.min_id.
            rewrite list_num_leaves_total.
            reflexivity.
          }
        }
        {
          exact pfyz'.
        }
        {
          do 3 f_equal.
          refine (eq_trans (eq_sym (zip_combine_err_zip_btree_err _ _ _ _ _)) _).
          {
            rewrite skipn_length.
            rewrite num_leaves_join.
            refine (eq_trans _ (f_equal
              (fun x => 
                (x -
                list_num_leaves
                (leaves
                (fmap_btree snd (zip_btree_err b (firstn (num_leaves b) ys) (bnil ())))))%nat
              )
              pfxy
            )).
            do 2 (rewrite list_num_leaves_total).
            rewrite <- (f_equal
              (fun x => total (map[Coq.listF] num_leaves x))
              (firstn_skipn (num_leaves b) ys)
            ).
            rewrite map_app.
            rewrite total_app.
            assert (H2 :
              total (List.map num_leaves (firstn (num_leaves b) ys)) =
              (total (map[Coq.listF] num_leaves
              (leaves
                 (fmap_btree snd
                    (zip_btree_err b (firstn (num_leaves b) ys) (bnil ()))))))%nat
            ).
            {
              rewrite leaves_fmap.
              assert (H2 :
                num_leaves b = length (firstn (num_leaves b) ys)
              ).
              {
                exact (list_num_leaves_firstn pfyz).
              }
              {
                rewrite (zip_btree_err_correct _ _ H2).
                rewrite leaves_zip_btree.
                rewrite list_map_snd_combine.
                rewrite eq_num_leaves.
                rewrite firstn_firstn.
                rewrite PeanoNat.Nat.min_id.
                reflexivity.
              }
            }
            {
              rewrite <- H2.
              rewrite Minus.minus_plus.
              reflexivity.
            }
          }
          {
            refine (list_num_leaves_skipn _).
            rewrite <- pfxy.
            rewrite <- (f_equal
              list_num_leaves
              (firstn_skipn (num_leaves b) ys)
            ).
            do 2 (rewrite list_num_leaves_total).
            rewrite map_app.
            rewrite total_app.
            simpl.
            rewrite total_equation_2.
            refine (nat_plus_eq _ eq_refl).
            rewrite num_leaves_join.
            rewrite leaves_fmap.
            assert (H2 :
              num_leaves b = length (firstn (num_leaves b) ys)
            ).
            {
              exact (list_num_leaves_firstn pfyz).
            }
            {
              rewrite (zip_btree_err_correct _ _ H2).
              rewrite leaves_zip_btree.
              rewrite list_map_snd_combine.
              rewrite eq_num_leaves.
              rewrite firstn_firstn.
              rewrite PeanoNat.Nat.min_id.
              rewrite list_num_leaves_total.
              reflexivity.
            }
          }
          {
            refine (eq_trans
              _
              (zip_combine_err_correct num_leaves zip_btree zip_btree_err zip_btree_err_correct
                _
                _
                H'
                (bnil tt)
              )
            ).
            assert (H'' :
                (skipn (num_leaves (join_btree (fmap_btree snd (zip_btree_err b (firstn (num_leaves b) ys) (bnil ()))))) xs) =
                (skipn (total (map[Coq.listF] num_leaves (firstn (num_leaves b) ys))) xs)
            ).
            {
              rewrite num_leaves_join.
              rewrite leaves_fmap.
              assert (H2 :
                num_leaves b = length (firstn (num_leaves b) ys)
              ).
              {
                exact (list_num_leaves_firstn pfyz).
              }
              {
                rewrite (zip_btree_err_correct _ _ H2).
                rewrite leaves_zip_btree.
                rewrite list_map_snd_combine.
                rewrite eq_num_leaves.
                rewrite firstn_firstn.
                rewrite PeanoNat.Nat.min_id.
                rewrite list_num_leaves_total.
                reflexivity.
              }
            }
            {
              rewrite <- H''.
              reflexivity.
            }
          }
        }
      }
    }
  }
}
Qed.

Lemma assoc_join_zip_btrees {xs ys zs : list (@btree 1)}
  (pfxy : list_num_leaves ys = length xs)
  (pfzxy : list_num_leaves zs = length (join_zip_btrees ys xs pfxy))
  (pfyz : list_num_leaves zs = length ys)
  (pfxyz : list_num_leaves (join_zip_btrees zs ys pfyz) = length xs) :
    join_zip_btrees
      (join_zip_btrees zs ys pfyz)
      xs
      pfxyz =
    join_zip_btrees
      zs
      (join_zip_btrees ys xs pfxy)
      pfzxy.
Local Transparent join_zip_btrees.
unfold join_zip_btrees in *.
Local Opaque join_zip_btrees.
repeat (repeat (rewrite <- (zip_btrees_err_correct _ _ _ (bnil tt)))).
exact (assoc_join_zip_btrees_err pfxy pfyz).
Qed.

