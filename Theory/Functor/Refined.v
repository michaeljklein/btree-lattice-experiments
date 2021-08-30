Set Warnings "-notation-overridden".

Require Import Coq.Program.Basics.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.Eqdep_dec.

From Equations Require Import Equations.
Unset Equations With Funext.

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Require Import Embed.Theory.Functor.Void.
Require Import Embed.Theory.Functor.Refined.Def.
Require Import Embed.Theory.Functor.Refined.Iso.
Require Import Embed.Theory.Functor.Refined.ToFrom.

Require Import Embed.Theory.Utils.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section EmbedRefined.
Context `{F : Coq ⟶ Coq}.

Class EmbedRefinedCat (G : RefinedCat ⟶ Coq) := {
  embed_iso_refined x y :
    iso_refined x y ↔ G x = G y;

  embed_refined x : G x;
  embed_refined_unique x (xs : G x) : embed_refined x = xs;

  run_embed_refined {x} (xs : G x) : F 1;

  cast_run_embed_refined {x y} (xs : G x) (pf : G x = G y) :
      run_embed_refined (cast pf xs) = run_embed_refined xs;

  fobj_run_embed_refined {x} (xs : G x) :
    G (run_embed_refined xs) = G x;

  canonical_refined (x : F 1) : F 1 :=
    run_embed_refined (embed_refined x);
}.

Context (G : RefinedCat ⟶ Coq).
Context {eqDecG : forall x, EqDec (G x)}.
Context {embedRefinedCatG : EmbedRefinedCat G}.

Lemma iso_refined_canonical_refined {x y : F 1} :
  iso_refined (canonical_refined x) y ↔ iso_refined x y.
split.

intro.
refine (snd (embed_iso_refined _ _) _).
pose (X' := fst (embed_iso_refined _ _) X).
unfold canonical_refined in *.
rewrite fobj_run_embed_refined in X'.
exact X'.

(* Practically the same proof as above *)
intro.
refine (snd (embed_iso_refined _ _) _).
pose (X' := fst (embed_iso_refined _ _) X).
unfold canonical_refined in *.
rewrite fobj_run_embed_refined.
exact X'.
Qed.

Lemma unfold_canonical_refined_eq {x y : F 1} :
    canonical_refined x = canonical_refined y ↔ iso_refined x y.
split.

unfold canonical_refined.
intro.
pose (H' := f_equal G H).
repeat (rewrite fobj_run_embed_refined in H').
exact (snd (embed_iso_refined x y) H').

intro.
unfold canonical_refined.
pose (X' := fst (embed_iso_refined x y) X).
pose (embed_refined_unique x (cast (eq_sym X') (embed_refined y))).
pose (f_equal run_embed_refined e).
rewrite cast_run_embed_refined in e0.
exact e0.
Qed.

Program Instance canonical_refined_Idempotent : Idempotent canonical_refined.
Next Obligation.
simpl.
refine (snd unfold_canonical_refined_eq _).
refine (snd (embed_iso_refined (canonical_refined x) x) _).
unfold canonical_refined.
rewrite fobj_run_embed_refined.
reflexivity.
Qed.

Context `{monadF : @Monad Coq F}.

Definition section (A : Type) (x y : F 1) : Type :=
    { z : F (F A) |
      canonical_refined (void[F] z) = canonical_refined x /\
      canonical_refined (void[F] (join[F] z)) = canonical_refined y
    }.

Lemma eq_section {A} {F1_dec : EqDec (F 1)} {x y : F 1} (xs ys : section A x y)
  (pf : proj1_sig xs = proj1_sig ys) : xs = ys.
destruct xs, ys.
unfold proj1_sig in pf.
refine (eq_sig
  (exist
  (λ z : F (F A),
   canonical_refined (void[F] z) = canonical_refined x /\
   canonical_refined (void[F] (join[F] z)) = canonical_refined y) x0 a)
  (exist
  (λ z : F (F A),
   canonical_refined (void[F] z) = canonical_refined x /\
   canonical_refined (void[F] (join[F] z)) = canonical_refined y) x1 a0)
  pf
  _
).
simpl.

destruct pf.
simpl.
refine (eq_and _ _).
Qed.

Definition fst_section {A} {x y : F 1} : section A x y -> F (F A) := @proj1_sig _ _.

Definition snd_section {A} {x y : F 1} (xy : section A x y) :
  canonical_refined (void[F] (fst_section xy)) = canonical_refined x /\
  canonical_refined (void[F] (join[F] (fst_section xy))) = canonical_refined y :=
    @proj2_sig _
      (fun z =>
        canonical_refined (void[F] z) = canonical_refined x /\
        canonical_refined (void[F] (join[F] z)) = canonical_refined y
      )
      _.

Lemma unfold_snd_section {A} {x y : F 1} (z : F (F A)) :
  canonical_refined (void[F] z) = canonical_refined x /\
  canonical_refined (void[F] (join[F] z)) = canonical_refined y ↔
  iso_refined (void[F] z) x *
  iso_refined (void[F] (join[F] z)) y.
split.

intro.
destruct H.
split.

pose (H' := f_equal canonical_refined H).
pose (idem_z := idem (void[F] z)).
simpl in idem_z.
rewrite idem_z in H'.
clear idem_z.
pose (H'' := Equivalence_Symmetric _ _ (fst unfold_canonical_refined_eq H')).
exact (Equivalence_Symmetric _ _ (fst iso_refined_canonical_refined H'')).

pose (H0' := f_equal canonical_refined H0).
pose (idem_z := idem (void[F] (join[F] z))).
simpl in idem_z.
rewrite idem_z in H0'.
clear idem_z.
pose (H0'' := Equivalence_Symmetric _ _ (fst unfold_canonical_refined_eq H0')).
exact (Equivalence_Symmetric _ _ (fst iso_refined_canonical_refined H0'')).

intro.
destruct X.
split.

exact (snd unfold_canonical_refined_eq i).

exact (snd unfold_canonical_refined_eq i0).
Qed.

(* TODO: Cleanup class definition *)
Class Iso_refined_void_join :=
  iso_refined_void_join : forall (x : F (F 1)) (y : F 1)
  (pf : iso_refined (join[F] x) y) (A : Type),
    @refined (Compose F F) x A ≅ refined y A.

Definition wrapped_section A : Type :=
  { i & section A (canonical_refined (ret[F] tt)) i }.

Lemma eq_wrapped_section {A} {F1_dec : EqDec (F 1)} (xs ys : wrapped_section A)
  (pf1 : projT1 xs = projT1 ys)
  (pf2 : proj1_sig (projT2 xs) = proj1_sig (projT2 ys)) : xs = ys.
destruct xs, ys.
destruct s, s0.
simpl in pf1, pf2.
destruct pf1.
destruct pf2.
rewrite (eq_and a a0).
reflexivity.
Qed.

Equations from_wrapped_section {A} (xs : wrapped_section A) : F A :=
from_wrapped_section xs := join[F] (proj1_sig (projT2 xs)).

Class Iso_refined_void_ret : Type := {
  iso_refined_void_ret {A} {x : F A}
    (pf : iso_refined (void[F] x) (ret tt)) :
      { y | ret y = x}
}.

Lemma iso_refined_void_ret_join {A} {Iso_refined_void_retF : Iso_refined_void_ret}
  (x : F (F A))
  (pf : iso_refined (void x) (ret tt)) :
  ret (join x) = x.
destruct (iso_refined_void_ret pf).
rewrite <- e.
pose (H := join_ret x0).
simpl in H.
rewrite H.
reflexivity.
Qed.

End EmbedRefined.

