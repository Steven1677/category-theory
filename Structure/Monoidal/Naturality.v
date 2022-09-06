Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Functor.Endo.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.
Set Transparent Obligations.

Section MonoidalNaturality.

Context `{M : @Monoidal C}.

Program Definition Tensor_Left {F : C ⟶ C} {y : C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ y)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] id
|}.
Next Obligation.
  proper; apply bimap_respects; rewrites; reflexivity.
Defined.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Left_Map `{@EndoFunctor C P} {y : C} :
  @EndoFunctor C (fun x => P x ⨂ y)%object := {
  map := fun _ _ f => map f ⨂ id;
  endo_is_functor := @Tensor_Left endo_is_functor _
}.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1.
  apply bifunctor_respects; simpl; split.
    apply fobj_related.
  reflexivity.
Defined.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1;
  unfold Tensor_Left_Map_obligation_2; simpl.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

#[export] Program Instance Tensor_Right {F : C ⟶ C} {x : C} : C ⟶ C := {
  fobj := fun y => (x ⨂ F y)%object;
  fmap := fun _ _ f => id ⨂[M] fmap[F] f
}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Right_Map `{@EndoFunctor C P} {x : C} :
  @EndoFunctor C (fun y => x ⨂ P y)%object := {
  map := fun _ _ f => id ⨂ map f;
  endo_is_functor := @Tensor_Right endo_is_functor _
}.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1.
  apply bifunctor_respects; simpl; split.
    reflexivity.
  apply fobj_related.
Defined.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1;
  unfold Tensor_Left_Map_obligation_2; simpl.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

Program Definition Tensor_Both `{F : C ⟶ C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ F x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] fmap[F] f
|}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Both_Map `{@EndoFunctor C P} :
  @EndoFunctor C (fun x => P x ⨂ P x)%object := {
  map := fun _ _ f => map f ⨂ map f;
  endo_is_functor := @Tensor_Both endo_is_functor
}.
Next Obligation.
  apply bifunctor_respects; simpl; split;
  apply fobj_related.
Defined.
Next Obligation.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

Theorem monoidal_naturality :
  natural (@unit_left _ M) *
  natural (@unit_right _ M) *
  natural (@tensor_assoc _ M).
Proof. prove_naturality M normal. Qed.

End MonoidalNaturality.
