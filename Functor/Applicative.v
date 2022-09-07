Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Balanced.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.

Generalizable All Variables.

(* An "applicative" functor is a strong lax monoidal functor in a monoidal
   closed category. *)

Section ApplicativeFunctor.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

Class Applicative := {
  applicative_is_strong : StrongFunctor F;
  applicative_is_lax_monoidal : LaxMonoidalFunctor F;

  ap {x y} : F (x ⇒ y) ⨂ F x ~> F y :=
    fmap[F] eval ∘ @lax_ap _ _ _ _ F _ (x ⇒ y) x
}.
#[export] Existing Instance applicative_is_strong.
#[export] Existing Instance applicative_is_lax_monoidal.

End ApplicativeFunctor.

Arguments pure {C _ F _ _ _}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 9, format "pure[ F ]") : morphism_scope.
