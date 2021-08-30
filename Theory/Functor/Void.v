Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.
Require Import Category.Instance.Coq.

Generalizable All Variables.
Set Universe Polymorphism.
Set Nested Proofs Allowed.

Section FunctorVoid.

Context `{C : Category}.
Context `{TerminalC : @Terminal C}.
Context `{F : C ⟶ C}.

Definition void {x} : F x ~> F 1 := fmap one.

Lemma void_fmap {x y} (f : x ~> y) :
  void ∘ fmap f ≈ void.
unfold void.
exact (Equivalence_Transitive _ _ _
  (Equivalence_Symmetric _ _ (@fmap_comp _ _ F x y 1 (@one C TerminalC y) f))
  (fmap_respects _ _ _ _ (@one_comp _ TerminalC x y f))
).
Qed.

End FunctorVoid.

Notation "void[ F ]" := (@void _ _ F _)
  (at level 9, format "void[ F ]") : category_scope.
Notation "void_fmap[ F ]" := (@void_fmap _ _ F _ _)
  (at level 9, format "void_fmap[ F ]") : category_scope.

Section FunctorVoidCoq.
Context `{F : Coq ⟶ Coq}.

Definition one_1 : one[1] ≈ id := one_unique one[1] id.

Lemma void_1 (x : F 1) :
  void x = x.
unfold void.
refine (eq_trans (@fmap_respects Coq Coq F _ _ _ _ one_1 x) _).
exact (fmap_id _).
Qed.

Lemma void_fmap_1 (x : F (F 1)) :
  fmap[F] void[F] x = x.
refine (eq_trans (@fmap_respects Coq Coq F _ _ _ _ void_1 x) _).
exact (fmap_id _).
Qed.

End FunctorVoidCoq.

Section MonadVoidCoq.

Context `{F : Coq ⟶ Coq}.
Context `{monadF : @Monad Coq F}.

Lemma void_join {A : Type} (x : F (F A)) :
  void[F] (join[F] x) = join[F] (fmap[F] void[F] x).
pose (H := join_fmap_fmap one[A] x).
simpl in H.
replace (fmap[F] void[F] x) with
        (fmap[F] (fmap[F] one[A]) x) by reflexivity.
simpl.
rewrite H.
reflexivity.
Qed.

End MonadVoidCoq.

