Require Export Category.

Generalizable All Variables.

Class Product `(C : Category objC)
  (P : objC) `(p1 : P ~> A) `(p2 : P ~> B) :=
{ product_ump :
    forall (X : objC) (x1 : X ~> A) (x2 : X ~> B),
       exists (u : X ~> P), x1 ≈ p1 ∘ u /\ x2 ≈ p2 ∘ u
    /\ forall (v : X ~> P), p1 ∘ v ≈ x1 /\ p2 ∘ v ≈ x2 -> v ≈ u
}.

(* Tuples in the Coq category satisfy the UMP for products.
*)
Program Instance Tuple_Product {X Y : Set}
  : Product Coq (X * Y) (@fst X Y) (@snd X Y).
Obligation 1. (* product ump *)
  exists (fun x => (x1 x, x2 x)).
  intros. constructor.
    intros. unfold fst. reflexivity.
  split.
    intros. unfold snd. reflexivity.
  intros.
  inversion H.
  specialize (H0 x). rewrite <- H0.
  specialize (H1 x). rewrite <- H1.
  destruct (v x).
  reflexivity.
Defined.