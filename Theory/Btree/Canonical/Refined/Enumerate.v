Set Warnings "-notation-overridden".

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FinFun.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.

Require Import Embed.Theory.Btree.
Require Import Embed.Theory.Btree.Canonical.
Require Import Embed.Theory.Btree.Functor.

Require Import Embed.Theory.Datatypes.List.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Equations enumerate_refined_canonical_btree_bool_helper (x : nat)
 (xs : refined (canonical_btree x) bool)
  : list (refined (canonical_btree (S x)) bool) :=
enumerate_refined_canonical_btree_bool_helper x (@exist _ _ xs pf) :=
  cons (@exist _ _ (bcons (bnil false) xs) _) (
  cons (@exist _ _ (bcons (bnil true) xs) _) nil).
Next Obligation.
rewrite canonical_btree_equation_2.
exact (bcons_eq eq_refl pf).
Defined.
Next Obligation.
rewrite canonical_btree_equation_2.
exact (bcons_eq eq_refl pf).
Defined.

Lemma enumerate_refined_canonical_btree_bool_helper_NoDup (x : nat) :
  forall xs, List.NoDup (enumerate_refined_canonical_btree_bool_helper x xs).
intros.
destruct xs.
rewrite enumerate_refined_canonical_btree_bool_helper_equation_1.
refine (List.NoDup_cons _ _ _).

intro.
simpl in H.
destruct H.

discriminate.

exact H.

refine (List.NoDup_cons _ _ _).

intro.
simpl in H.
exact H.

exact (List.NoDup_nil _).
Qed.

Equations enumerate_refined_canonical_btree_bool (x : nat) :
  list (refined (canonical_btree x) bool) :=
enumerate_refined_canonical_btree_bool O :=
  cons (@exist _ _ (bnil false) eq_refl) (
  cons (@exist _ _ (bnil true) eq_refl) nil);
enumerate_refined_canonical_btree_bool (S x) :=
  List.flat_map
    (enumerate_refined_canonical_btree_bool_helper x)
    (enumerate_refined_canonical_btree_bool x).

Fixpoint enumerate_refined_canonical_btree_bool_all (x : nat)
  (y : refined (canonical_btree x) bool) :
    List.In y (enumerate_refined_canonical_btree_bool x).
destruct x.

destruct y.
destruct x.

rewrite enumerate_refined_canonical_btree_bool_equation_1.
destruct b.

simpl.
refine (or_intror _).
refine (or_introl _).
Local Transparent canonical_btree.
unfold canonical_btree in e.
simpl in e.
Local Opaque canonical_btree.
rewrite (UIP_dec dec_eq_btree e eq_refl).
reflexivity.

simpl.
refine (or_introl _).
Local Transparent canonical_btree.
unfold canonical_btree in e.
simpl in e.
Local Opaque canonical_btree.
rewrite (UIP_dec dec_eq_btree e eq_refl).
reflexivity.

simpl.
Local Transparent canonical_btree.
unfold canonical_btree in e.
simpl in e.
Local Opaque canonical_btree.
discriminate.

destruct y.
Local Transparent canonical_btree.
unfold canonical_btree in e.
destruct x0.

simpl in e.
discriminate.

simpl in e.
destruct (distribute_eq_bcons e).
destruct x0_1.

2: {
  simpl in H.
  discriminate.
}

simpl in H.
simpl in e.
rewrite enumerate_refined_canonical_btree_bool_equation_2.
refine (proj2 (List.in_flat_map
  (enumerate_refined_canonical_btree_bool_helper x)
  (enumerate_refined_canonical_btree_bool x)
  _
) _
).

pose (xx := (@exist _ _ x0_2 H0) : refined (canonical_btree x) bool).
pose (xx' := enumerate_refined_canonical_btree_bool_all x xx).
refine (@ex_intro
  (refined (canonical_btree x) bool)
  (fun x0 : refined (canonical_btree x) bool =>
  List.In x0 (enumerate_refined_canonical_btree_bool x) /\
  List.In
    (exist
       (λ y : btree_Functor bool,
        void[btree_Functor] y = canonical_btree (S x)) 
       (bcons (bnil b) x0_2) e)
    (enumerate_refined_canonical_btree_bool_helper x x0)
  )
  xx
  (conj xx' _)
).
unfold xx.
Local Transparent enumerate_refined_canonical_btree_bool_helper.
simpl.
destruct b.

refine (or_intror _).
refine (or_introl _).
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
rewrite <- (eq_rect_eq_dec dec_eq_btree).
exact (UIP_dec dec_eq_btree _ _).

refine (or_introl _).
refine (eq_exist_uncurried _).
refine (@exist _ _ eq_refl _).
rewrite <- (eq_rect_eq_dec dec_eq_btree).
exact (UIP_dec dec_eq_btree _ _).
Qed.


Lemma enumerate_refined_canonical_btree_bool_helper_Injectives (x : nat) :
  Injectives (enumerate_refined_canonical_btree_bool_helper x).
proper.
destruct x0, y.
repeat (rewrite enumerate_refined_canonical_btree_bool_helper_equation_1 in H).
repeat (rewrite enumerate_refined_canonical_btree_bool_helper_equation_1 in H0).

destruct H, H0.

destruct H.
destruct (proj2 (distribute_eq_bcons (EqdepFacts.eq_sig_fst H0))).
refine (eq_exist_uncurried (@exist _ _ eq_refl _)).
simpl.
exact (UIP_dec dec_eq_btree _ _).

destruct H.
destruct H0.
destruct (proj2 (distribute_eq_bcons (EqdepFacts.eq_sig_fst H))).
refine (eq_exist_uncurried (@exist _ _ eq_refl _)).
simpl.
exact (UIP_dec dec_eq_btree _ _).

destruct H.

destruct H.
destruct H.
destruct (proj2 (distribute_eq_bcons (EqdepFacts.eq_sig_fst H0))).
refine (eq_exist_uncurried (@exist _ _ eq_refl _)).
simpl.
exact (UIP_dec dec_eq_btree _ _).

destruct H.

destruct H.

destruct H.
destruct H0.

destruct (proj2 (distribute_eq_bcons (EqdepFacts.eq_sig_fst H))).
refine (eq_exist_uncurried (@exist _ _ eq_refl _)).
simpl.
exact (UIP_dec dec_eq_btree _ _).

destruct H.

destruct H.
Qed.


Fixpoint enumerate_refined_canonical_btree_bool_nodup (x : nat) :
  List.NoDup (enumerate_refined_canonical_btree_bool x).
destruct x.

rewrite enumerate_refined_canonical_btree_bool_equation_1.
refine (List.NoDup_cons _ _ _).

intro.
destruct H.

discriminate.

destruct H.

refine (List.NoDup_cons _ _ (List.NoDup_nil _)).
intro.
destruct H.

rewrite enumerate_refined_canonical_btree_bool_equation_2.
refine (Injectives_flat_map_NoDup _ _ _ _ (enumerate_refined_canonical_btree_bool_nodup x)).

exact (enumerate_refined_canonical_btree_bool_helper_Injectives _).

exact (enumerate_refined_canonical_btree_bool_helper_NoDup _).
Qed.

Fixpoint length_flat_map_enumerate_refined_canonical_btree_bool_helper (x : nat)
  (xs : list (refined (canonical_btree x) bool)) :
  length (List.flat_map (enumerate_refined_canonical_btree_bool_helper x) xs) = (2 * length xs)%nat.
destruct xs.

reflexivity.

simpl.
destruct r.
rewrite enumerate_refined_canonical_btree_bool_helper_equation_1.
simpl.

rewrite PeanoNat.Nat.add_succ_r.
refine (eq_S _ _ _).
refine (eq_S _ _ _).
pose (H := length_flat_map_enumerate_refined_canonical_btree_bool_helper x xs).
simpl in H.
exact H.
Qed.

Fixpoint enumerate_refined_canonical_btree_bool_length (x : nat) :
  length (enumerate_refined_canonical_btree_bool x) = Nat.pow 2 (S x).
destruct x.

reflexivity.

rewrite enumerate_refined_canonical_btree_bool_equation_2.
rewrite length_flat_map_enumerate_refined_canonical_btree_bool_helper.
replace (Nat.pow 2 (S (S x))) with (2 * Nat.pow 2 (S x))%nat by reflexivity.
rewrite (enumerate_refined_canonical_btree_bool_length x).
reflexivity.
Qed.

Fixpoint enumerate_refined_canonical_btree_bool_length_eq (x y : nat)
  (pf : length (enumerate_refined_canonical_btree_bool x) = length (enumerate_refined_canonical_btree_bool y)) :
    x = y.
rewrite (enumerate_refined_canonical_btree_bool_length x) in pf.
rewrite (enumerate_refined_canonical_btree_bool_length y) in pf.
pose (pf' := PeanoNat.Nat.pow_inj_r 2%nat (S x) (S y) PeanoNat.Nat.lt_1_2 pf).
exact (eq_add_S _ _ pf').
Qed.

