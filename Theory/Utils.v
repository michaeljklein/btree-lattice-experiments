Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Local Open Scope nat_scope.

Equations nat_plus_eq {x y z w : nat} (xz : x = z) (yw : y = w) : (x + y) = (z + w) :=
nat_plus_eq eq_refl eq_refl := eq_refl.

Equations list_app_eq {A} {x y z w : list A} (xz : x = z) (yw : y = w) : (x ++ y) = (z ++ w) :=
list_app_eq eq_refl eq_refl := eq_refl.

Definition length_cons_eq {A B} {x : A} {xs : list A} {y : B} {ys : list B}
  (pf : length xs = length ys) :
    length (x :: xs) = length (y :: ys) := eq_S _ _ pf.

Lemma combine_nil_r {A B} (x : list A) : combine x (@nil B) = nil.
destruct x.
reflexivity.

reflexivity.
Defined.

Equations list_cons_eq {A} {x z : A} {y w : list A} (xz : x = z) (yw : y = w) : cons x y = cons z w :=
list_cons_eq eq_refl eq_refl := eq_refl.

Fixpoint combine_app {A B} (x y : list A) (z : list B) :
  combine (x ++ y) z = combine x (firstn (length x) z) ++ combine y (skipn (length x) z).
destruct x.

reflexivity.

destruct z.

unfold length.
unfold firstn.
unfold skipn.
repeat (rewrite combine_nil_r).
reflexivity.

replace ((a :: x) ++ y) with (a :: (x ++ y)) by reflexivity.
replace (length (a :: x)) with (S (length x)) by reflexivity.
replace (firstn (S (length x)) (b :: z)) with (b :: firstn (length x) z) by reflexivity.
replace (skipn (S (length x)) (b :: z)) with (skipn (length x) z) by reflexivity.
replace (combine (a :: x ++ y) (b :: z)) with (pair a b :: combine (x ++ y) z) by reflexivity.
replace (combine (a :: x) (b :: firstn (length x) z)) with (pair a b :: combine x (firstn (length x) z)) by reflexivity.
exact (list_cons_eq eq_refl (combine_app _ _ x y z)).
Defined.

Lemma list_map_cons {A B} (f : A -> B) (x : A) (xs : list A) : List.map f (cons x xs) = cons (f x) (List.map f xs).
reflexivity.
Defined.

Fixpoint list_map_snd_combine {A B} (xs : list A) (ys : list B) :
  List.map snd (combine xs ys) = firstn (length xs) ys.
destruct xs.

reflexivity.

destruct ys.

reflexivity.

replace (combine (a :: xs) (b :: ys)) with (pair a b :: combine xs ys) by reflexivity.
replace (firstn (length (a :: xs)) (b :: ys)) with (b :: firstn (length xs) ys) by reflexivity.
replace (List.map snd ((a, b) :: combine xs ys)) with (b :: List.map snd (combine xs ys)) by reflexivity.
refine (list_cons_eq eq_refl _).
exact (list_map_snd_combine A B xs ys).
Defined.

Lemma refine_nat_pred_positive {x y : nat} : forall
  (posX : x <> 0) (posY : y <> 0)
  (pf : x - 1 = y - 1), x = y.
intros.
destruct x, y.

destruct (posX eq_refl).

destruct (posX eq_refl).

destruct (posY eq_refl).

clear posX.
clear posY.
simpl in pf.
repeat (rewrite PeanoNat.Nat.sub_0_r in pf).
exact (f_equal S pf).
Qed.

Local Close Scope nat_scope.

Section ListDepHd.

Equations dep_hd {A} (xs : list A) (pf : xs <> []) : A :=
dep_hd nil pf := False_rect A (pf eq_refl) ;
dep_hd (cons x _) _ := x.

Lemma eq_dep_hd {A} (xs : list A) (pf : xs <> []) (x : A) :
  dep_hd xs pf = hd x xs.
destruct xs.

pose (pf eq_refl).
destruct f.

reflexivity.
Qed.

End ListDepHd.

Lemma eq_and {A} {A_dec : EqDec A} {x y z w : A} (xs ys : x = y /\ z = w) : xs = ys.
destruct xs, ys.
destruct e, e0.
pose (H := @UIP_dec A A_dec x x eq_refl e1).
destruct H.
pose (H := @UIP_dec A A_dec z z eq_refl e2).
destruct H.
reflexivity.
Qed.

(* TODO: Replace other usage(s) of PeanoNat.Nat.add_min_distr_l with thi *)
Lemma nat_min_plus (x y : nat) :
  Nat.min x (x + y) = x.
replace (Nat.min x) with
        (Nat.min (x + 0)) by
        (rewrite <- plus_n_O; reflexivity).
rewrite PeanoNat.Nat.add_min_distr_l.
rewrite PeanoNat.Nat.min_0_l.
rewrite <- plus_n_O.
reflexivity.
Qed.

Equations cast {A B : Type} (pf : A = B) : A -> B :=
cast pf x := @eq_rect _ A Datatypes.id x B pf.

