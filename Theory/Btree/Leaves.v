Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.

Require Import Embed.Theory.Utils.
Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Functor.
Require Import Embed.Theory.Btree.Monad.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations num_leaves {A} (xs : @btree A) : nat :=
num_leaves (bnil _) := S O ;
num_leaves (bcons x y) := num_leaves x + num_leaves y.
Global Transparent num_leaves.

Lemma num_leaves_positive {A} (xs : @btree A) : ~(num_leaves xs = O).
Proof.
revert xs.
fix num_leaves_positive 1.
destruct xs.

rewrite num_leaves_equation_1.
auto.

rewrite num_leaves_equation_2.
intro.
pose (Plus.plus_is_O (num_leaves xs1) (num_leaves xs2) H).
destruct a.
exact (num_leaves_positive xs1 H0).
Qed.

Lemma num_leaves_fmap {A B} {f : A -> B} (xs : @btree A) : num_leaves (fmap f xs) = num_leaves xs.
Proof.
revert xs.
fix num_leaves_fmap 1.
destruct xs.

rewrite fmap_btree_equation_1.
repeat (rewrite num_leaves_equation_1).
reflexivity.

rewrite fmap_btree_equation_2.
repeat (rewrite num_leaves_equation_2).

refine (nat_plus_eq _ _).

exact (num_leaves_fmap _).

exact (num_leaves_fmap _).
Qed.

Equations leaves {A} (xs : @btree A) : list A :=
leaves (bnil x) := cons x nil ;
leaves (bcons x y) := leaves x ++ leaves y.

Fixpoint leaves_fmap {A B} (f : A -> B) (xs : @btree A) :
  leaves (fmap_btree f xs) = List.map f (leaves xs).
destruct xs.

rewrite fmap_btree_equation_1.
repeat (rewrite leaves_equation_1).
reflexivity.

rewrite fmap_btree_equation_2.
repeat (rewrite leaves_equation_2).
rewrite map_app.

refine (list_app_eq _ _).

exact (leaves_fmap _ _ _ _).

exact (leaves_fmap _ _ _ _).
Qed.

Lemma eq_num_leaves {A} (xs : @btree A) : length (leaves xs) = num_leaves xs.
Proof.
revert xs.
fix eq_num_leaves 1.
destruct xs.

rewrite leaves_equation_1.
rewrite num_leaves_equation_1.
unfold length.
reflexivity.

rewrite leaves_equation_2.
rewrite num_leaves_equation_2.
rewrite app_length.
refine (nat_plus_eq _ _).

exact (eq_num_leaves _).

exact (eq_num_leaves _).
Qed.

Local Open Scope nat_scope.

(* lemma for zip_btree *)
Lemma num_leaves_bcons_length_l {A B} {x y : @btree A} {ys : list B} : num_leaves (bcons x y) = length ys
  -> num_leaves x <= length ys.
intro.
rewrite num_leaves_equation_2 in H.
rewrite <- H.
exact (Plus.le_plus_l _ _).
Qed.

Definition num_leaves_firstn {A B} {x y : @btree A} {zs : list B} (pf : num_leaves (bcons x y) = length zs) :
  num_leaves x = length (firstn (num_leaves x) zs) := eq_sym
    (firstn_length_le zs (num_leaves_bcons_length_l pf)).

Definition num_leaves_skipn {A B} {x y : @btree A} {zs : list B} (pf : num_leaves (bcons x y) = length zs) :
   num_leaves y = length (skipn (num_leaves x) zs) := eq_sym
        (eq_trans
          (skipn_length (num_leaves x) zs)
          (eq_sym
            (Minus.plus_minus (length zs) (num_leaves x) (num_leaves y) (eq_sym pf))
          )
        ).

(* list_num_leaves xs = sum (map num_leaves xs) *)
Equations list_num_leaves {A} (xs : list (@btree A)) : nat :=
list_num_leaves nil := O ;
list_num_leaves (cons y ys) := num_leaves y + list_num_leaves ys.

Lemma eq_num_leaves_list_num_leaves {A} (xs : @btree A) : num_leaves xs = list_num_leaves (cons xs nil).
Proof.
rewrite list_num_leaves_equation_2.
rewrite list_num_leaves_equation_1.
auto.
Qed.

Lemma list_num_leaves_cons_positive {A} (x : @btree A) (xs : list (@btree A)) :
  list_num_leaves (x :: xs) <> 0%nat.
Proof.
revert xs; revert x.
fix list_num_leaves_cons_positive 2.
destruct xs.

rewrite <- eq_num_leaves_list_num_leaves.
exact (num_leaves_positive _).

rewrite list_num_leaves_equation_2.
intro.
refine (list_num_leaves_cons_positive b xs _).
pose (Plus.plus_is_O _ _ H).
destruct a.
exact H1.
Qed.

Lemma list_num_leaves_map_fmap {A B} {xs : list (@btree A)} (f : A → B) :
  list_num_leaves (List.map (fmap[btree_Functor] f) xs) = list_num_leaves xs.
Proof.
revert xs.
fix list_num_leaves_map_fmap 1.
destruct xs.

simpl.
reflexivity.

unfold List.map.
repeat (rewrite list_num_leaves_equation_2).
refine (nat_plus_eq _ _).

exact (num_leaves_fmap _).

exact (list_num_leaves_map_fmap xs).
Qed.

Equations total : list nat -> nat :=
total nil := 0%nat;
total (cons x xs) := x + total xs.

Fixpoint total_app (xs ys : list nat) :
  total (xs ++ ys) = (total xs + total ys)%nat.
destruct xs.
{
  reflexivity.
}
{
  rewrite total_equation_2.
  simpl.
  rewrite total_equation_2.
  rewrite <- PeanoNat.Nat.add_assoc.
  f_equal.
  exact (total_app _ _).
}
Qed.

Fixpoint list_num_leaves_total {A : Type} (xs : list (@btree A)) :
  list_num_leaves xs = total (map num_leaves xs).
destruct xs.
{
  rewrite list_num_leaves_equation_1.
  simpl.
  rewrite total_equation_1.
  reflexivity.
}
{
  rewrite list_num_leaves_equation_2.
  simpl.
  rewrite total_equation_2.
  rewrite (list_num_leaves_total A xs).
  reflexivity.
}
Qed.

(* Local Open Scope nat_scope. *)
Lemma list_num_leaves_app {A} (xs ys : list (@btree A)) :
  (list_num_leaves xs + list_num_leaves ys)%nat = list_num_leaves (xs ++ ys).
do 3 (rewrite list_num_leaves_total).
rewrite map_app.
rewrite total_app.
reflexivity.
Qed.

Fixpoint num_leaves_join {A} (xs : @btree (@btree A)) :
  num_leaves (join_btree xs) = list_num_leaves (leaves xs).
destruct xs.

rewrite join_btree_equation_1.
rewrite leaves_equation_1.
rewrite list_num_leaves_equation_2.
rewrite list_num_leaves_equation_1.
exact (plus_n_O _).

rewrite join_btree_equation_2.
rewrite leaves_equation_2.
rewrite num_leaves_equation_2.
rewrite <- list_num_leaves_app.
refine (nat_plus_eq _ _).

exact (num_leaves_join _ _).

exact (num_leaves_join _ _).
Qed.

Local Open Scope nat_scope.
Definition list_num_leaves_firstn {A B} {z : @btree A} {zs : list (@btree A)} {ws : list B}
  (pf : list_num_leaves (z :: zs) = length ws) :
    num_leaves z = length (firstn (num_leaves z) ws) := eq_sym
  (firstn_length_le
    ws
    (eq_rect (num_leaves z + list_num_leaves zs) (fun w => num_leaves z <= w) (Plus.le_plus_l (num_leaves z) (list_num_leaves zs)) (length ws) (eq_trans (eq_sym (list_num_leaves_equation_2 A z zs)) pf))
  ).
Local Close Scope nat_scope.

Definition list_num_leaves_skipn {A B} {z : @btree A} {zs : list (@btree A)} {ws : list B}
  (pf : list_num_leaves (z :: zs) = length ws) :
    list_num_leaves zs = length (skipn (num_leaves z) ws) := eq_sym
  (eq_trans
    (skipn_length (num_leaves z) ws)
    (eq_sym
      (Minus.plus_minus (length ws) (num_leaves z) (list_num_leaves zs) (eq_sym pf))
    )
  ).

