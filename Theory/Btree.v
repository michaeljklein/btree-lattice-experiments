Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Cumulative Inductive btree {A : Type} : Type :=
  | bnil : A -> btree
  | bcons : btree -> btree -> btree.

Derive NoConfusion NoConfusionHom for btree.
Derive Subterm for btree.
Next Obligation.
apply Subterm.WellFounded_trans_clos.
intro x; revert x.
fix wf_btree 1.
intro x.
apply Acc_intro.
intro y; intro yx.
destruct x; inversion yx; apply wf_btree.
Defined.

Lemma not_btree_direct_subterm_bnil {A} (x : @btree A) (ys : A) :
  notT (btree_direct_subterm A x (bnil ys)).
intro H.
inversion H.
Qed.

Lemma not_btree_subterm_bnil {A} (x : @btree A) : forall (ys : A),
  notT (btree_subterm A x (bnil ys)).
intros ys H.
revert H.
revert x.
fix not_btree_subterm_bnil 2.
intros x H.
inversion H.
- exact (not_btree_direct_subterm_bnil _ _ H0).
- exact (not_btree_subterm_bnil _ H1).
Qed.

Lemma not_btree_direct_subterm_bcons {A} (x ys zs : @btree A)
  (pfy : x ≠ ys)
  (pfz : x ≠ zs)
  : notT (btree_direct_subterm A x (bcons ys zs)).
intro H.
inversion H.
- apply pfz in H3; assumption.
- apply pfy in H2; assumption.
Qed.

Existing Instance NoConfusionPackage_btree.
Existing Instance NoConfusionHomPackage_btree.
Existing Instance well_founded_btree_subterm.

Equations bnil_eq {A} {x y : A} : x = y -> bnil x = bnil y :=
bnil_eq eq_refl := eq_refl.

Equations bcons_eq {A} {x y z w : @btree A} (xz : x = z) (yw : y = w) : bcons x y = bcons z w :=
bcons_eq eq_refl eq_refl := eq_refl.

Equations distribute_eq_bnil {A} {x y : A} (xs : bnil x = bnil y) : x = y :=
distribute_eq_bnil eq_refl := eq_refl.

Equations distribute_eq_bcons {A} {x y z w : @btree A} (xs : bcons x y = bcons z w) : x = z /\ y = w :=
distribute_eq_bcons eq_refl := conj eq_refl eq_refl.

Equations lift_eq_bnil {A} {x y : A} :
  (x = y ∨ x ≠ y) ->
  ((bnil x = bnil y) ∨ (bnil x ≠ bnil y)) :=
lift_eq_bnil (Specif.left eq_refl) := Specif.left eq_refl;
lift_eq_bnil (Specif.right pfXY) := Specif.right (fun pfXYs => pfXY (distribute_eq_bnil pfXYs)).

Equations lift_eq_bcons {A} {x y z w : @btree A} :
  (x = y ∨ x ≠ y) ->
  (z = w ∨ z ≠ w) ->
  ((bcons x z = bcons y w) ∨ (bcons x z ≠ bcons y w)) :=
lift_eq_bcons (Specif.left eq_refl) (Specif.left eq_refl) := Specif.left eq_refl ;
lift_eq_bcons (Specif.left eq_refl) (Specif.right pfZW) :=
  Specif.right (fun eqXZW => pfZW (proj2 (distribute_eq_bcons eqXZW))) ;
lift_eq_bcons (Specif.right pfXY) (Specif.left eq_refl) :=
  Specif.right (fun eqXZY => pfXY (proj1 (distribute_eq_bcons eqXZY))) ;
lift_eq_bcons (Specif.right pfXY) (Specif.right _) :=
  Specif.right (fun pfXZYW => pfXY (proj1 (distribute_eq_bcons pfXZYW))).

Equations dec_eq_btree {A} `{EqDecA : EqDec A} : EqDec (@btree A) :=
dec_eq_btree (bnil xs) (bnil ys) := lift_eq_bnil (EqDecA xs ys) ;
dec_eq_btree (bnil _) (bcons xs ys) := Specif.right _ ;
dec_eq_btree (bcons xs ys) (bnil _) := Specif.right _ ;
dec_eq_btree (bcons xs ys) (bcons zs ws) := lift_eq_bcons (dec_eq_btree xs zs) (dec_eq_btree ys ws).

Existing Instance dec_eq_btree.

Equations dec_btree_direct_subterm {A} `{EqDecA : EqDec A} (x y : @btree A) :
  btree_direct_subterm A x y \/
  ~btree_direct_subterm A x y :=
dec_btree_direct_subterm x (bnil ys) := or_intror (not_btree_direct_subterm_bnil x ys);
dec_btree_direct_subterm x (bcons ys zs) with (dec_eq_btree x ys) => {
  dec_btree_direct_subterm x (bcons ?(x) zs) (Specif.left eq_refl) :=
    or_introl (btree_direct_subterm_1_2 _ _ _);
  dec_btree_direct_subterm x (bcons ys zs) (Specif.right _) with (dec_eq_btree x zs) => {
  dec_btree_direct_subterm x (bcons ys ?(x)) (Specif.right _) (Specif.left eq_refl) :=
    or_introl (btree_direct_subterm_1_1 _ _ _);
  dec_btree_direct_subterm x (bcons ys zs) (Specif.right pfy) (Specif.right pfz) :=
    or_intror (not_btree_direct_subterm_bcons x ys zs pfy pfz)
  }
}.

Class DecSubterm {A : Type} (R : A -> A -> Prop) := {
  dec_subterm (x y : A) : R x y \/ ~R x y
}.

Program Instance dec_subterm_btree_direct_subterm {A} `{EqDecA : EqDec A} : DecSubterm (btree_direct_subterm A) := {}.
Next Obligation.
exact (dec_btree_direct_subterm _ _).
Qed.

Lemma split_clos_trans_l {A} (R : Relation_Definitions.relation A) (x y : A) :
  Relation_Operators.clos_trans A R x y <-> exists z, R x z /\ (y = z \/ Relation_Operators.clos_trans A R z y).

split.
{
  intro xy.
  apply Operators_Properties.clos_trans_t1n in xy.
  inversion xy.
  {
    refine (@ex_intro _ _ y0 _).
    refine (conj _ _).
    {
      rewrite <- H0 in H.
      assumption.
    }
    {
      refine (or_introl _).
      symmetry.
      assumption.
    }
  }
  {
    refine (@ex_intro _ _ y0 _).
    refine (conj _ _).
    {
      assumption.
    }
    {
      refine (or_intror _).
      apply Operators_Properties.clos_t1n_trans in H0.
      assumption.
    }
  }
}
{
  intro xy.
  inversion xy.
  inversion H.
  inversion H1.
  {
    rewrite <- H2 in H0.
    refine (Relation_Operators.t_step _ _ _ _ _).
    assumption.
  }
  {
    refine (Relation_Operators.t_trans _ _ _ _ _ (Relation_Operators.t_step _ _ _ _ H0) _).
    assumption.
  }
}
Qed.

(* Almost the same proof as split_clos_trans_l *)
Lemma split_clos_trans_r {A} (R : Relation_Definitions.relation A) (x y : A) :
  Relation_Operators.clos_trans A R x y <-> exists z, R z y /\ (x = z \/ Relation_Operators.clos_trans A R x z).
split.
{
  intro xy.
  apply Operators_Properties.clos_trans_tn1 in xy.
  inversion xy.
  {
    refine (@ex_intro _ _ x _).
    refine (conj _ _).
    {
      assumption.
    }
    {
      refine (or_introl _).
      reflexivity.
    }
  }
  {
    refine (@ex_intro _ _ y0 _).
    refine (conj _ _).
    {
      assumption.
    }
    {
      refine (or_intror _).
      apply Operators_Properties.clos_tn1_trans in H0.
      assumption.
    }
  }
}
{
  intro xy.
  inversion xy.
  inversion H.
  inversion H1.
  {
    rewrite <- H2 in H0.
    refine (Relation_Operators.t_step _ _ _ _ _).
    assumption.
  }
  {
    refine (Relation_Operators.t_trans _ _ _ _ _ _ (Relation_Operators.t_step _ _ _ _ H0)).
    assumption.
  }
}
Qed.


Lemma btree_direct_subterm_bcons {A} (x y z : @btree A) :
  btree_direct_subterm A x (bcons y z) <->
  ((x = y) \/ (x = z)).
split.
{
  intro H.
  inversion H.
  - exact (or_intror eq_refl).
  - exact (or_introl eq_refl).
}
{
  intro H.
  destruct H as [H | H]; rewrite H.
  - exact (btree_direct_subterm_1_2 _ _ _).
  - exact (btree_direct_subterm_1_1 _ _ _).
}
Qed.

Lemma distribute_or_and (x y z : Prop) :
  (x \/ y) /\ z <-> x /\ z \/ y /\ z.
tauto.
Qed.

Lemma distribute_ex_and_eq {A} (f g : A -> Prop) (x : A) :
  (exists y : A, y = x /\ f y \/ g y) <->
  f x \/ (exists y : A, g y).
split; intro H.
{
  destruct H.
  destruct H.
  {
    refine (or_introl _).
    destruct H.
    rewrite H in H0.
    assumption.
  }
  {
    refine (or_intror _).
    exact (ex_intro _ _ H).
  }
}
{
  destruct H.
  {
    refine (ex_intro _ x _).
    tauto.
  }
  {
    destruct H as (y & H).
    refine (ex_intro _ y _).
    tauto.
  }
}
Qed.

Lemma or_False_id_r (x : Prop) :
  x <-> x \/ False.
tauto.
Qed.

Lemma ex_False (A : Type) :
  (exists _ : A, False) <-> False.
intuition.
destruct H.
assumption.
Qed.

Lemma btree_subterm_bcons {A} (x y z : @btree A) :
  btree_subterm A x (bcons y z) <->
  x = y \/
  x = z \/
  btree_subterm A x y \/
  btree_subterm A x z.
refine (iff_Transitive _ _ _ (split_clos_trans_r _ x (bcons y z)) _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun x' => and_iff_compat_r _ (btree_direct_subterm_bcons x' _ _))) _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => distribute_or_and _ _ _)) _).
refine (iff_Transitive _ _ _ (distribute_ex_and_eq _ _ _) _).
rewrite or_assoc.
refine (or_iff_compat_l _ _).
rewrite <- (or_assoc (x = z) (btree_subterm A x y) (btree_subterm A x z)).
rewrite (or_comm (x = z) (btree_subterm A x y)).
rewrite (or_assoc (btree_subterm A x y) (x = z) (btree_subterm A x z)).
refine (or_iff_compat_l _ _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => and_comm _ _)) _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => distribute_or_and _ _ _)) _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => or_iff_compat_r _ (and_comm _ _))) _).
refine (iff_Transitive _ _ _ (distribute_ex_and_eq _ _ _) _).
refine (or_iff_compat_l _ _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => and_comm _ _)) _).
refine (iff_Transitive _ _ _ (Morphisms_Prop.ex_iff_morphism _ _ (fun _ => or_False_id_r _)) _).
refine (iff_Transitive _ _ _ (distribute_ex_and_eq _ _ _) _).
rewrite (ex_False _).
rewrite <- (or_False_id_r _).
reflexivity.
Qed.

Fixpoint dec_btree_subterm {A} `{EqDecA : EqDec A} (x y : @btree A) :
  btree_subterm A x y \/
  ~btree_subterm A x y.
destruct y.
{
  exact (or_intror (not_btree_subterm_bnil _ _)).
}
{
  rewrite btree_subterm_bcons.
  destruct (dec_eq_btree x y1).
  {
    refine (or_introl _).
    refine (or_introl _).
    assumption.
  }
  {
    destruct (dec_eq_btree x y2).
    {
      refine (or_introl _).
      refine (or_intror _).
      refine (or_introl _).
      assumption.
    }
    {
      destruct (dec_btree_subterm _ _ x y1).
      {
        refine (or_introl _).
        refine (or_intror _).
        refine (or_intror _).
        refine (or_introl _).
        assumption.
      }
      {
        destruct (dec_btree_subterm _ _ x y2).
        {
          refine (or_introl _).
          refine (or_intror _).
          refine (or_intror _).
          refine (or_intror _).
          assumption.
        }
        {
          refine (or_intror _).
          clear dec_btree_subterm.
          tauto.
        }
      }
    }
  }
}
Qed.

Program Instance dec_subterm_btree_subterm {A} `{EqDecA : EqDec A} : DecSubterm (btree_subterm A) := {}.
Next Obligation.
exact (dec_btree_subterm _ _).
Qed.

Ltac is_btree_subterm :=
  solve [
  repeat (assumption || match goal with
  | |- btree_subterm ?A ?x ?y =>
         exact (Relation_Operators.t_step _ _ _ _ (btree_direct_subterm_1_1 _ _ _))
      || exact (Relation_Operators.t_step _ _ _ _ (btree_direct_subterm_1_2 _ _ _))
      || refine (Relation_Operators.t_trans _ _ _ _ _ _ (Relation_Operators.t_step _ _ _ _ (btree_direct_subterm_1_1 _ _ _)))
      || refine (Relation_Operators.t_trans _ _ _ _ _ _ (Relation_Operators.t_step _ _ _ _ (btree_direct_subterm_1_2 _ _ _)))
  end)
  ] ||
  match goal with
  | |- ?H => gfail 0 "is_btree_subterm failed" H
  end.

Definition is_btree_subterm_ex1 : btree_subterm () (bnil tt) (bcons (bnil tt) (bcons (bnil tt) (bnil tt))) :=
  ltac:(is_btree_subterm).

Definition is_btree_subterm_ex2 : btree_subterm () (bnil tt) (bcons (bnil tt) (bnil tt)) :=
  ltac:(is_btree_subterm).

Fail Definition is_btree_subterm_ex3 : btree_subterm () (bcons (bnil tt) (bnil tt)) (bnil tt) :=
  ltac:(is_btree_subterm).

