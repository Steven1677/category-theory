Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Eilenberg.Moore.

Section KT.

(* Global Set Transparent Obligations. *)

Definition KT: forall (C: Category)
               (D: Category)
               (F : C ⟶ D)
               (G : D ⟶ C)
               (A : F ∹ G),
               let M   := Adjunction_Nat_Monad A in
               let EMC := @EilenbergMoore C (G ◯ F) M in
               D ⟶ EMC.
Proof. intros.
       cbn in *.
       unshelve econstructor.
       - simpl. intro X.
         exists (fobj[G] X).
         unshelve econstructor.
         + exact (fmap[G] (transform[counit] X)).
         + simpl in *.
           destruct A.
           simpl in *.
           rewrite fmap_counit_unit. easy.
         + simpl.
           rewrite <- !fmap_comp.
           destruct counit.
           simpl in *.
           rewrite naturality. easy.
       - simpl. intros.
         unshelve econstructor.
         + exact (fmap[G] f).
         + simpl. rewrite <- !fmap_comp.
           destruct counit.
           simpl in *.
           rewrite naturality. easy.
       - repeat intro. cbn.
         rewrite X. easy.
       - cbn. intros.
         rewrite fmap_id. easy.
       - cbn. intros. rewrite fmap_comp. easy.
Defined.

Definition FT {C: Category} {T: @Functor C C} (M: @Monad C T)
              (EMC := (@EilenbergMoore C T M)): @Functor C EMC.
Proof. intros.
       unshelve econstructor.
       - intro X. simpl.
         exists (fobj[T] X).
         + unshelve econstructor.
           ++ exact(join[T]).
           ++ rewrite join_ret. easy.
           ++ rewrite join_fmap_join. easy.
       - simpl. intros.
         unshelve econstructor.
         + simpl. exact (fmap[T] f).
         + simpl. rewrite join_fmap_fmap. easy.
       - repeat intro. simpl.
         rewrite X. easy.
       - simpl. intros.
         rewrite fmap_id. easy.
       - simpl. intros. rewrite fmap_comp. easy. 
Defined.

Definition GT {C  : Category} {T: @Functor C C} (M  : @Monad C T)
              (EMC:= (@EilenbergMoore C T M)): @Functor EMC C.
Proof. unshelve econstructor.
       - simpl. intros (a, Ta). exact a.
       - simpl. intros (a, Ta) (b, Tb) (c, Tc). simpl in *.
         exact c.
       - simpl. intros (a, Ta) (b, Tb).
         repeat intro. simpl. easy.
       - simpl. intros (a, Ta). easy.
       - simpl.  intros (a, Ta) (b, Tb) (c, Tc) f g. simpl in *.
         easy.
Defined.

Lemma commKT: forall (C: Category)
                     (D: Category)
                     (F : C ⟶ D)
                     (G : D ⟶ C)
                     (A : F ∹ G),
                     let M   := Adjunction_Nat_Monad A in
                     let EMC := @EilenbergMoore C (G ◯ F) M in
                     (((GT M) ◯ (KT C D F G A)) ≈ G) * ((KT C D F G A) ◯ F ≈ (FT M)).
Proof. intros. split.
       - simpl.
         unshelve econstructor.
         simpl. intros. rewrite id_left, id_right. easy.
       - simpl.
         unshelve econstructor.
         + intros. cbn.
           unshelve econstructor.
           ++ simpl.
              unshelve econstructor.
              +++ simpl. exact id.
              +++ simpl.
                  rewrite <- fmap_comp.
                  rewrite fmap_id.
                  rewrite id_left, id_right. easy.
           ++ simpl.
              unshelve econstructor.
              +++ simpl. exact id.
              +++ simpl.
                  rewrite <- fmap_comp.
                  rewrite fmap_id.
                  rewrite id_left, id_right. easy.
           ++ cbn. rewrite id_left. easy.
           ++ cbn. rewrite id_left. easy.
         + intros. simpl.
           rewrite id_left, id_right. easy.
Qed.

Lemma KUniqe: forall (C: Category)
                     (D: Category)
                     (F : C ⟶ D)
                     (G : D ⟶ C)
                     (A : F ∹ G),
                     let M   := Adjunction_Nat_Monad A in
                     let EMC := @EilenbergMoore C (G ◯ F) M in
                       forall (R: @Functor D EMC), ((((GT M) ◯ R) ≈ G) * ((R ◯ F) ≈ (FT M))) -> 
                              (KT C D F G A) ≈ R.
Proof. intros.
       simpl.
       unshelve econstructor.
       - intros.
         unshelve econstructor.
         + simpl.
           unshelve econstructor.
           ++ simpl. simpl in X.
              destruct X as ((u,H1),(v,H2)).
              cbn in *.
              clear H1.
              specialize(u x). 
              destruct u. exact from.
           ++ destruct X as ((u,H1),(v,H2)).
              cbn in *.
              clear H1.
              destruct(u x).
              cbn in *.
              destruct A, counit.
              cbn in *.
Admitted.

End KT.