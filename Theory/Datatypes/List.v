Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.

Require Import Embed.Theory.Utils.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

(* TODO: Move other similiar lemmas from utils *)
Equations distribute_eq_cons {A} {x y : A} {xs ys : list A} (pf : cons x xs = cons y ys) : x = y /\ xs = ys :=
distribute_eq_cons eq_refl := conj eq_refl eq_refl.

Definition Injectives {A B : Type} (f : A -> list B) :=
  forall (x y : A) (z : B), List.In z (f x) -> List.In z (f y) -> x = y.

Fixpoint nodup_app_disjoint {A} (xs ys : list A) :
  (forall z, List.In z xs -> List.In z ys -> False) ->
  List.NoDup xs -> List.NoDup ys -> List.NoDup (xs ++ ys).
intros.
destruct xs.

simpl.
exact H1.

refine (proj2 (List.NoDup_cons_iff a (xs ++ ys)) _).
split.

intro.
destruct (List.in_app_or xs ys a H2).

exact (proj1 (proj1 (List.NoDup_cons_iff a xs) H0) H3).

refine (H a _ H3).
simpl.
exact (or_introl eq_refl).

pose (H0' := proj2 (proj1 (List.NoDup_cons_iff a xs) H0)).
refine (nodup_app_disjoint A xs ys _ H0' H1).
intros.
refine (H z _ H3).
exact (List.in_cons a z xs H2).
Qed.

Fixpoint Injectives_flat_map_NoDup {A B} (f : A -> list B) (xs : list A) :
  Injectives f -> (forall a, List.NoDup (f a)) -> List.NoDup xs -> List.NoDup (List.flat_map f xs).
intros.
destruct xs.

simpl.
exact (List.NoDup_nil _).

simpl.
refine (nodup_app_disjoint _ _ _ _ _).

intros.
destruct (proj1 (List.in_flat_map f xs z) H3).
destruct H4.
refine (proj1 (proj1 (List.NoDup_cons_iff a xs) H1) _).
rewrite <- (H a x z H2 H5) in H4.
exact H4.

exact (H0 a).

refine (Injectives_flat_map_NoDup A B f xs H H0 _).
exact (proj2 (proj1 (List.NoDup_cons_iff a xs) H1)).
Qed.


(* From Coq 8.12 ..... *)
Lemma in_in_remove : forall A eq_dec (l : list A) x y, x <> y -> In x l -> In x (remove eq_dec y l).
Proof.
  induction l as [|z l]; simpl; intros x y Hneq Hin.
  - apply Hin.
  - destruct (eq_dec y z); subst.
    + destruct Hin.
      * exfalso; now apply Hneq.
      * now apply IHl.
    + simpl; destruct Hin; [now left|right].
      now apply IHl.
Qed.

Definition AllIn {A : Type} (xs ys : list A) : Type :=
  forall z, List.In z xs -> List.In z ys.

Lemma Full_to_AllIn {A : Type} (xs ys : list A) (fullYs : Full ys) :
  AllIn xs ys.
proper.
Qed.

Lemma nodup_allin_cons_remove {A : Type} {eqDecA : EqDec A} {x : A} {xs ys : list A} :
  List.NoDup (x :: xs) ->
  AllIn (x :: xs) ys ->
  AllIn xs (List.remove eqDecA x ys).
proper.
unfold AllIn in X.
destruct (eqDecA x z).

rewrite <- e in H0.
destruct (proj1 (proj1 (List.NoDup_cons_iff x xs) H) H0).

exact (in_in_remove _ _ ys z x (fun pf => n (eq_sym pf)) (X z (or_intror H0))).
Qed.

Fixpoint length_remove_in {A : Type} {A_eq_dec : ∀ x y : A, x = y ∨ x ≠ y}
  (x : A) (xs : list A) :
    List.In x xs -> (length (remove A_eq_dec x xs) < length xs)%nat.
intro.
destruct xs.

destruct H.

simpl.
destruct (A_eq_dec x a).

refine (Lt.le_lt_n_Sm _ _ _).
exact (length_remove _ _ _ _).

destruct H.

destruct (n (eq_sym H)).

simpl.
refine (Lt.lt_n_S _ _ _).
exact (length_remove_in A A_eq_dec x xs H).
Qed.

Fixpoint nodup_pigeonhole {A} {eqDecA : EqDec A} (xs ys : list A) :
  List.NoDup xs -> AllIn xs ys -> (length xs <= length ys)%nat.
intros.
destruct xs.

simpl.
exact (PeanoNat.Nat.le_0_l _).

simpl.
refine (Lt.lt_le_S _ _ _).
destruct (proj1 (List.NoDup_cons_iff a xs) H).
pose (X' := nodup_allin_cons_remove H X).
pose (le_remove := nodup_pigeonhole A eqDecA xs (remove eqDecA a ys) H1 X').
pose (remove_lt := @length_remove_in A eqDecA a ys (X a (or_introl eq_refl))).
exact (PeanoNat.Nat.le_lt_trans _ _ _ le_remove remove_lt).
Qed.


Equations dec_eq_list {A} {EqDecA : EqDec A} : EqDec (list A) :=
dec_eq_list nil nil := Specif.left _ ;
dec_eq_list nil (cons _ _) := Specif.right _ ;
dec_eq_list (cons _ _) nil := Specif.right _ ;
dec_eq_list (cons x xs) (cons y ys) with (pair (EqDecA x y) (dec_eq_list xs ys)) => {
  dec_eq_list (cons x xs) (cons y ys) (pair (Specif.left eq_refl) (Specif.left eq_refl)) :=
    Specif.left eq_refl ;
  dec_eq_list (cons x xs) (cons y ys) (pair (Specif.right _) (Specif.left eq_refl)) :=
    Specif.right _ ;
  dec_eq_list (cons x xs) (cons y ys) (pair (Specif.left eq_refl) (Specif.right _)) :=
    Specif.right _ ;
  dec_eq_list (cons x xs) (cons y ys) (pair (Specif.right _) (Specif.right _)) :=
    Specif.right _
}.

Fixpoint list_map_const_seq {A : Type} (x : A) (a b c : nat) :
  List.map (fun _ : nat => x) (seq a c) = List.map (fun _ : nat => x) (seq b c).
destruct c.
{
  reflexivity.
}
{
  simpl.
  refine (list_cons_eq eq_refl _).
  exact (list_map_const_seq _ _ _ _ _).
}
Qed.

Fixpoint firstn_map {A B : Type} (f : A -> B) (n : nat) (xs : list A) :
  firstn n (List.map f xs) = List.map f (firstn n xs).
destruct xs.
{
  repeat (rewrite firstn_nil).
  reflexivity.
}
{
  destruct n.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite firstn_map.
    reflexivity.
  }
}
Qed.

(* Proof is firstn_map: s/firstn/skipn/g *)
Fixpoint skipn_map {A B : Type} (f : A -> B) (n : nat) (xs : list A) :
  skipn n (List.map f xs) = List.map f (skipn n xs).
destruct xs.
{
  repeat (rewrite skipn_nil).
  reflexivity.
}
{
  destruct n.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite skipn_map.
    reflexivity.
  }
}
Qed.

Fixpoint firstn_seq (x y z : nat) :
  firstn x (seq y z) = seq y (Nat.min x z).
destruct x.
{
  reflexivity.
}
{
  destruct z.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite firstn_seq.
    reflexivity.
  }
}
Qed.

(* Almost the same as s/firstn/skipn/g on firstn_seq *)
Fixpoint skipn_seq (x y z : nat) :
  skipn x (seq y z) = seq (x + y) (z - x).
destruct x.
{
  rewrite PeanoNat.Nat.sub_0_r.
  reflexivity.
}
{
  destruct z.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite skipn_seq.
    rewrite PeanoNat.Nat.add_succ_r.
    reflexivity.
  }
}
Qed.

Fixpoint skipn_skipn {A : Type} (x y : nat) (zs : list A) :
  skipn x (skipn y zs) = skipn (y + x) zs.
destruct y.
{
  reflexivity.
}
{
  destruct zs.
  {
    simpl.
    rewrite skipn_nil.
    reflexivity.
  }
  {
    rewrite PeanoNat.Nat.add_succ_l.
    do 2 (rewrite skipn_cons).
    exact (skipn_skipn _ _ _ _).
  }
}
Qed.

Fixpoint skipn_skipn_positive_cons {A : Type} (n m : nat) (pf : n <> 0%nat) (x : A) (xs : list A) :
  skipn n (skipn m (x :: xs)) = skipn n (x :: skipn m xs).
destruct n.
{
  destruct (pf eq_refl).
}
{
  rewrite skipn_cons.
  destruct xs.
  {
    do 2 (rewrite skipn_nil).
    destruct m.
    {
      simpl.
      rewrite skipn_nil.
      reflexivity.
    }
    {
      simpl.
      rewrite skipn_nil.
      reflexivity.
    }
  }
  {
    (* pose (pf' := fun ys => pf *) 
    destruct n.
    {
      do 2 (rewrite skipn_skipn).
      rewrite <- plus_n_O.
      rewrite PeanoNat.Nat.add_1_r.
      rewrite skipn_cons.
      reflexivity.
    }
    {
      assert (pf' : S n <> 0%nat).
      {
        intro.
        discriminate.
      }
      {
        rewrite (skipn_skipn_positive_cons A (S n) m pf' a xs).
        clear skipn_skipn_positive_cons.
        destruct m.
        {
          reflexivity.
        }
        {
          do 2 (rewrite skipn_cons).
          do 2 (rewrite skipn_skipn).
          rewrite PeanoNat.Nat.add_succ_r.
          rewrite skipn_cons.
          f_equal.
          rewrite PeanoNat.Nat.add_succ_comm.
          reflexivity.
        }
      }
    }
  }
}
Qed.

Lemma skipn_app_length {A} (xs ys : list A) :
  skipn (length xs) (xs ++ ys) = ys.
refine (eq_trans (@skipn_app A (length xs) xs ys) _).
rewrite skipn_all.
simpl.
rewrite PeanoNat.Nat.sub_diag.
exact (skipn_O _).
Qed.

