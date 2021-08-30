Set Warnings "-notation-overridden".
From Equations Require Import Equations.

Require Import Equations.Type.Loader.

Require Import Category.Lib.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Leaves.

Generalizable All Variables.
Set Universe Polymorphism.
Import Sigma_Notations.
Import Id_Notations.
Local Open Scope equations_scope.

Set Equations Transparent.


Section BtreeDepth.

Equations depth {A : Type} (xs : @btree A) : nat :=
depth (bnil _) := O;
depth (bcons x y) := S (Nat.max (depth x) (depth y)).

End BtreeDepth.


Fixpoint max_spec (n m : nat) :
     ((n < m)%nat ∧ eq (PeanoNat.Nat.max n m) m) +
     ((m <= n)%nat ∧ eq (PeanoNat.Nat.max n m) n).
destruct n, m;
  solve [ refine (inl _); refine (pair _ _); intuition ] +
  solve [ refine (inr _); refine (pair _ _); intuition ] +
  idtac.
{
  destruct (max_spec n m).
  {
    destruct p.
    refine (inl (pair _ _));
    simpl;
    intuition.
  }
  {
    destruct p.
    refine (inr (pair _ _));
    simpl;
    intuition.
  }
}
Qed.

Fixpoint num_leaves_le_pow2_depth {A : Type} (x : @btree A) :
  (num_leaves x <= Nat.pow 2 (depth x))%nat.
destruct x.
{
  exact (le_n _).
}
{
  simpl.
  rewrite PeanoNat.Nat.add_0_r.
  refine (PeanoNat.Nat.add_le_mono _ _ _ _ _ _);
  refine (PeanoNat.Nat.le_trans _ _ _ (num_leaves_le_pow2_depth _ _) _);
  clear num_leaves_le_pow2_depth;
  refine (PeanoNat.Nat.pow_le_mono_r _ _ _ (PeanoNat.Nat.neq_succ_0 _) _).
  apply PeanoNat.Nat.le_max_l.
  apply PeanoNat.Nat.le_max_r.
}
Qed.

Section BtreeSubtermDepth.

Lemma btree_direct_subterm_depth {A : Type} (x y : @btree A)
  (xy : btree_direct_subterm A x y) :
  (depth x < depth y)%nat.
destruct y;
inversion xy;
rewrite depth_equation_2;
destruct (max_spec (depth y1) (depth y2)) as [(l & e) | (l & e)];
rewrite e;
(apply PeanoNat.Nat.lt_succ_diag_r ||
  apply le_n_S in l; exact l ||
  apply le_S_n in l; apply le_S in l; exact l
).
Qed.

Lemma trans_clos_incl {A : Type} {R S : Relation_Definitions.relation A}
  `{transitiveR : Transitive A S} :
  RelationClasses.subrelation R S ->
  RelationClasses.subrelation (Relation_Operators.clos_trans A R) S.
intro x.
intro y.
revert y.
revert x.
fix trans_clos_incl 4.
intro f.
intro x.
intro y.
intro xy.
destruct xy.
{
  exact (f _ _ H).
}
{
  exact (transitiveR x y z
    (trans_clos_incl f x y xy1)
    (trans_clos_incl f y z xy2)
  ).
}
Qed.

Program Instance lt_Transitive : Transitive lt := PeanoNat.Nat.lt_trans.

Program Instance lt_Transitive_f {A : Type} {f : A -> nat} : Transitive (fun x y => (f x < f y)%nat) := _.
Next Obligation.
intros.
apply (PeanoNat.Nat.lt_trans (f x) (f y) (f z)); assumption.
Qed.

Lemma btree_subterm_depth {A : Type} (x y : @btree A)
  (xy : btree_subterm A x y) :
  (depth x < depth y)%nat.
apply (trans_clos_incl btree_direct_subterm_depth) in xy.
assumption.
Qed.

End BtreeSubtermDepth.

