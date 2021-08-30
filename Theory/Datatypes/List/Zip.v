Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Datatypes.List.
Require Import Embed.Theory.Datatypes.List.Total.

Require Import Embed.Theory.Btree.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Lemma zip_combine_helper_firstn {A B}
  (f : A -> nat)
  (z : A) (zs : list A) (ws : list B)
  (pf : total (map f (z :: zs)) = length ws) :
    f z = length (firstn (f z) ws).
rewrite firstn_length.
rewrite <- pf.
simpl.
rewrite total_equation_2.
rewrite nat_min_plus.
reflexivity.
Qed.

Lemma zip_combine_helper_skipn {A B}
  (f : A -> nat)
  (z : A) (zs : list A) (ws : list B)
  (pf : total (map f (z :: zs)) = length ws) :
    total (map f zs) = length (skipn (f z) ws).
rewrite skipn_length.
rewrite <- pf.
simpl.
rewrite total_equation_2.
rewrite Minus.minus_plus.
reflexivity.
Qed.

Equations zip_combine {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), f x = length ys -> C)
  (xs : list A) (ys : list B)
  (pf : total (map f xs) = length ys) : list C :=
zip_combine _ _ nil _ _ := nil;
zip_combine f fs (cons z zs) ws pf :=
  cons
    (fs z
      (firstn (f z) ws)
      (zip_combine_helper_firstn f z zs ws pf)
    )
    (zip_combine f fs zs
      (skipn (f z) ws)
      (zip_combine_helper_skipn f z zs ws pf)
    ).

Equations zip_combine_err {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), B -> C)
  (xs : list A) (ys : list B)
  (err : B) : list C :=
zip_combine_err _ _ nil _ := fun _ => nil;
zip_combine_err f fs (cons z zs) ws := fun err =>
  cons
    (fs z
      (firstn (f z) ws)
      err
    )
    (zip_combine_err f fs zs
      (skipn (f z) ws)
      err
    ).

Fixpoint zip_combine_err_correct {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), f x = length ys -> C)
  (fs_err : forall (x : A) (ys : list B), B -> C)
  (fs_err_correct : forall (x : A) (ys : list B) (pf : f x = length ys) (err : B),
      fs_err x ys err = fs x ys pf
  )
  (xs : list A) (ys : list B) : forall
  (pf : total (map f xs) = length ys)
  (err : B),
    zip_combine_err f fs_err xs ys err = zip_combine f fs xs ys pf.
intros.
destruct xs.
{
  rewrite zip_combine_err_equation_1.
  rewrite zip_combine_equation_1.
  reflexivity.
}
{
  rewrite zip_combine_err_equation_2.
  rewrite zip_combine_equation_2.
  refine (list_cons_eq _ _).
  {
    exact (fs_err_correct _ _ _ _).
  }
  {
    exact (zip_combine_err_correct _ _ _ _ _ _ fs_err_correct _ _ _ _).
  }
}
Qed.

Fixpoint firstn_zip_combine_err {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), B -> C)
  (n : nat)
  (xs : list A) (ys : list B) : forall
  (pf : total (map f xs) = length ys)
  (err : B),
    firstn n (zip_combine_err f fs xs ys err) =
    zip_combine_err f fs (firstn n xs) (firstn (total (map f (firstn n xs))) ys) err.
intros.
destruct n.
{
  simpl.
  rewrite total_equation_1.
  reflexivity.
}
{
  destruct xs.
  {
    do 2 (rewrite zip_combine_err_equation_1).
    rewrite firstn_nil.
    reflexivity.
  }
  {
    rewrite zip_combine_err_equation_2.
    do 2 (rewrite firstn_cons).
    rewrite zip_combine_err_equation_2.
    simpl.
    rewrite total_equation_2.
    refine (list_cons_eq _ _).
    {
      f_equal.
      rewrite firstn_firstn.
      f_equal.
      rewrite nat_min_plus.
      reflexivity.
    }
    {
      rewrite firstn_zip_combine_err.
      {
        f_equal.
        rewrite firstn_skipn_comm.
        reflexivity.
      }
      {
        rewrite skipn_length.
        rewrite <- pf.
        simpl.
        rewrite total_equation_2.
        rewrite Minus.minus_plus.
        reflexivity.
      }
    }
  }
}
Qed.

(* Almost the same proof as firstn_zip_combine_err *)
Fixpoint skipn_zip_combine_err {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), B -> C)
  (n : nat)
  (xs : list A) (ys : list B) : forall
  (pf : total (map f xs) = length ys)
  (err : B),
    skipn n (zip_combine_err f fs xs ys err) =
    zip_combine_err f fs (skipn n xs) (skipn (total (map f (firstn n xs))) ys) err.
intros.
destruct n.
{
  simpl.
  rewrite total_equation_1.
  reflexivity.
}
{
  destruct xs.
  {
    do 2 (rewrite zip_combine_err_equation_1).
    rewrite skipn_nil.
    reflexivity.
  }
  {
    rewrite zip_combine_err_equation_2.
    do 2 (rewrite skipn_cons).
    rewrite firstn_cons.
    simpl.
    rewrite total_equation_2.
    rewrite skipn_zip_combine_err.
    {
      f_equal.
      rewrite skipn_skipn.
      reflexivity.
    }
    {
      rewrite skipn_length.
      rewrite <- pf.
      simpl.
      rewrite total_equation_2.
      rewrite Minus.minus_plus.
      reflexivity.
    }
  }
}
Qed.

Fixpoint firstn_zip_combine {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), f x = length ys -> C)
  (fs_err : forall (x : A) (ys : list B), B -> C)
  (fs_err_correct : forall (x : A) (ys : list B) (pf : f x = length ys) (err : B),
      fs_err x ys err = fs x ys pf
  )
  (n : nat)
  (xs : list A) (ys : list B) : forall
  (pf : total (map f xs) = length ys)
  (pf' : total (map[Coq.listF] f (firstn n xs)) =
    length (firstn (total (map[Coq.listF] f (firstn n xs))) ys)
  )
  (err : B),
    firstn n (zip_combine f fs xs ys pf) =
    zip_combine f fs (firstn n xs) (firstn (total (map f (firstn n xs))) ys) pf'.
intros.
do 2 (rewrite <- (zip_combine_err_correct f fs fs_err fs_err_correct _ _ _ err)).
exact (firstn_zip_combine_err _ _ _ _ _ pf _).
Qed.

(* Effectively the same wrapper as skipn_zip_combine *)
Fixpoint skipn_zip_combine {A B C}
  (f : A -> nat)
  (fs : forall (x : A) (ys : list B), f x = length ys -> C)
  (fs_err : forall (x : A) (ys : list B), B -> C)
  (fs_err_correct : forall (x : A) (ys : list B) (pf : f x = length ys) (err : B),
      fs_err x ys err = fs x ys pf
  )
  (n : nat)
  (xs : list A) (ys : list B) : forall
  (pf : total (map f xs) = length ys)
  (pf' : total (map[Coq.listF] f (skipn n xs)) =
    length (skipn (total (map[Coq.listF] f (firstn n xs))) ys)
  )
  (err : B),
    skipn n (zip_combine f fs xs ys pf) =
    zip_combine f fs (skipn n xs) (skipn (total (map f (firstn n xs))) ys) pf'.
intros.
do 2 (rewrite <- (zip_combine_err_correct f fs fs_err fs_err_correct _ _ _ err)).
exact (skipn_zip_combine_err _ _ _ _ _ pf _).
Qed.

