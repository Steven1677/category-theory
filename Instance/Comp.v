Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(*** Most of what follows in this file was written by Andrej Bauer:

     https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
*)

Module UniversalAlgebra.

(** In universal algebra, a (many-sorted) signature lists the operations that
    characterize an algebraic structure. Signatures play the same role in
    mathematics as type signatures in computer programming.

    We start by defining operation signatures. These describe the operations
    of an algebra.

    The main trick is that the arity of an operation is *not* a number but
    rather a type. For instance, the arity of a binary operation is a type
    with two elements. (And nothing prevents us from having an infinite type
    as arity.) *)
Record OpSignature := {
  operation : Type ;             (* (Names of) operations. *)
  arity     : operation → Type  (* Each operation has an arity. *)
}.

Arguments arity {_} _.

(** We shall consider algebras with given operations, but without equations.
    We call these "operation algebras". *)
Record OpAlgebra (S : OpSignature) := {
  carrier :> Type ;
  op : ∀ o : operation S, (arity o → carrier) → carrier
  (* no equations *)
}.

Arguments carrier {_} _.
Arguments op {_} _ _ _.

(** We define the type of homomorphism between operation algebras A and B. *)
Record AlgHom {S : OpSignature} (A : OpAlgebra S) (B : OpAlgebra S) := {
  map :> A → B ; (* The underlying map *)
  (* The underlying map commutes with operations: *)
  op_commute : ∀ (o : operation S) (args : arity o → A),
    map (op A o args) = op B o (fun x => map (args x))
}.

Arguments map {_ _ _} _.

#[export] Program Instance AlgHom_Setoid
    {S : OpSignature} (A : OpAlgebra S) (B : OpAlgebra S) :
  Setoid (AlgHom A B) := {|
  equiv := fun f g : AlgHom A B => ∀ x : A, f x = g x
|}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

Section FreeAlg.
  Hypothesis S : OpSignature.
  Hypothesis X : Type.

  (* The free algebra for a given signature [S] generated by [X]. *)
  Inductive Tree : Type :=
    | generator : X → Tree
    | node : ∀ (o : operation S), (arity o → Tree) → Tree.

  Definition Free : OpAlgebra S := {|
    carrier := Tree;
    op      := node
  |}.

  (* We show that the free algebra has the desired universal property. *)

  Hypothesis A : OpAlgebra S.
  Hypothesis h : X → A.

  Fixpoint induced_map (t : Tree) : A :=
    match t with
    | generator x => h x
    | node o arg => op A o (fun i => induced_map (arg i))
    end.

  Definition induced_hom : AlgHom Free A.
  Proof using A S X h.
    exists induced_map.
    intros o arg.
    reflexivity.
  Defined.

  (* The induced homomorphism is unique. *)
  Theorem from_free_unique (f g : AlgHom Free A) :
    (∀ x : X, f (generator x) = g (generator x)) → f ≈ g.
  Proof.
    intros eq_gen t.
    induction t.
    - now apply eq_gen.
    - rewrite 2 op_commute.
      f_equal.
      extensionality x.           (* jww (2020-02-23): How to remove this axiom? *)
      now apply H.
  Qed.
End FreeAlg.

Section Algs.

Context {S : OpSignature}.

Program Definition Alg_id (X : OpAlgebra S) : AlgHom X X :=
  {| map := fun x => x |}.

Program Definition Alg_comp (X Y Z : OpAlgebra S)
        (f : AlgHom Y Z) (g : AlgHom X Y) :=
  {| map := fun x => map f (map g x) |}.
Next Obligation. now rewrite 2 op_commute. Qed.

(** The category [Algs] for an algebraic signature S has as objects all
    algebras of that signature, and as morphisms all homomorphisms between
    them. *)

Program Instance Algs : Category := {
  obj     := OpAlgebra S;
  hom     := AlgHom;
  homset  := AlgHom_Setoid;
  id      := Alg_id;
  compose := Alg_comp
}.
Next Obligation. proper. now rewrite H, H0. Qed.

Program Instance Algs_Terminal : @Terminal Algs := {
  terminal_obj := {| carrier := unit : Type; op := fun _ _ => tt |};
  one := fun x : OpAlgebra S => {| map := fun a => tt |}
}.
Next Obligation.
  destruct f, g; simpl in *.
  now destruct (map0 x0), (map1 x0).
Qed.

Program Instance Algs_Cartesian : @Cartesian Algs := {
  product_obj := fun x y => {|
    carrier := x * y : Type;
    op := fun o k => (op x o (fun a => fst (k a)),
                      op y o (fun a => snd (k a)))
  |};
  fork := fun _ _ _ f g => {| map := fun x => (f x, g x) |};
  exl  := fun _ _ => {| map := fst |};
  exr  := fun _ _ => {| map := snd |}
}.
Next Obligation. now rewrite 2 op_commute. Qed.
Next Obligation. proper. now rewrite H, H0. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - rewrite <- H, <- H0.
    now rewrite <- surjective_pairing.
Qed.

(*
Program Instance Algs_Closed : @Closed Algs _ := {
  exponent_obj := fun x y => {|
    carrier := AlgHom x y;
    op := fun o k => {|
      map := fun r => op y o (fun a => k a r)
    |}
  |};
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f => {|
       map := fun x => {| map := fun y => f (x, y)
     |} |} |}
     ; from := {| morphism := fun f => {|
       map := fun p => f (fst p) (snd p)
     |} |} |}
}.
*)

(** In a category of algebras for some signature S, the free object is always
    initial. *)
Program Instance Algs_Initial : Initial Algs := {
  (* jww (2020-02-23): Is it right to be using False here? *)
  terminal_obj := Free S False;
  one := fun x : OpAlgebra S => induced_hom S False x (False_rect _)
}.
Next Obligation. now apply from_free_unique. Qed.

(*
Program Instance Algs_Cocartesian : @Cocartesian Algs := {
  product_obj := fun x y => {|
    carrier := x + y : Type;
    op := fun o k => _
  |};
  fork := _;
  exl  := _;
  exr  := _
}.
*)

End Algs.

(* Now given some operations, described by an operation signature S,
   we can define an equation signature which specifies some equations.
*)
Record EqSignature (S : OpSignature) := {
  eq :> Type ; (* (names of) equations *)

  (* each equation has an arity, which is the number of parameters appearing in it.
  Again, we use a type instead of a number. *)
  eq_arity : eq → Type ;

  (* Next we specify the equations. Note that they are polymorphic in the underlying algebra. *)
  lhs : ∀ (A : OpAlgebra S) (e : eq), (eq_arity e → A) → A ; (* left-hand sides *)
  rhs : ∀ (A : OpAlgebra S) (e : eq), (eq_arity e → A) → A ; (* right-hand sides *)

  (* Moreover, we require that the lhs and rhs are natural transformations, i.e,
     that they commute with homomorphism. This way it's impossible to write down
     strange equations that involve something other than the operations. *)
  lhs_natural :
    ∀ (A B : OpAlgebra S) (f : AlgHom A B) (e : eq) (args : eq_arity e → A),
      f (lhs A e args) = lhs B e (fun i => f (args i)) ;
  rhs_natural :
    ∀ (A B : OpAlgebra S) (f : AlgHom A B) (e : eq) (args : eq_arity e → A),
      f (rhs A e args) = rhs B e (fun i => f (args i)) ;
}.

Arguments eq_arity {_} {_} _.
Arguments lhs {_} {_} {_} _ _.
Arguments rhs {_} {_} {_} _ _.

(* We can now define what it means to have an algebra for a signature S satisfying
   equations E. *)
Record Algebra (S : OpSignature) (E : EqSignature S) := {
  alg :> OpAlgebra S ;
  equations : ∀ (e : E) (args : eq_arity e → alg), lhs e args = rhs e args
}.

(* We define some handy arities. *)
Inductive nullary : Set := .
Inductive unary : Set := Only.
Inductive binary : Set := Fst | Snd.
Inductive ternary : Set := One | Two | Three.

Section Examples.

(* Let us write down the definition of a group. As you can see this is extremely painful
   and long. *)

(* Group operations *)
Inductive Group_operation :=
  | one : Group_operation  (* unit *)
  | mul : Group_operation  (* multiplication *)
  | inv : Group_operation. (* inverse *)

Definition Group_arity (o : Group_operation) :=
  match o with
    | one => nullary
    | mul => binary
    | inv => unary
  end.

(* The structure of a group, but without equations. *)
Definition GroupOp := {|
  operation := Group_operation ;
  arity := Group_arity
|}.

(* Auxiliary functions that will make it easier to write down equations. *)

Definition one' {G : OpAlgebra GroupOp} :=
  op G one (fun i => match i with end).

Definition mul' {G : OpAlgebra GroupOp} (x y : G) :=
  op G mul (fun i => match i with
                       | Fst => x
                       | Snd => y
                     end).

Definition inv' {G : OpAlgebra GroupOp} (x : G) :=
  op G inv (fun _ => x).

(* There are five group equations. *)
Inductive Group_equation :=
  | assoc : Group_equation
  | unit_left : Group_equation
  | unit_right : Group_equation
  | inv_left : Group_equation
  | inv_right : Group_equation.

(* The arities of group equations. *)
Definition Group_eq_arity (e : Group_equation) :=
  match e with
    | assoc => ternary
    | unit_left => unary
    | unit_right => unary
    | inv_left => unary
    | inv_right => unary
  end.

(* The left-hand sides of group equations *)
Definition Group_lhs (A : OpAlgebra GroupOp) (e : Group_equation) :
  (Group_eq_arity e → A) → A :=
  match e with
    | assoc => (fun args => mul' (args One) (mul' (args Two) (args Three)))
    | unit_left => (fun args => mul' one' (args Only))
    | unit_right => (fun args => mul' (args Only) one')
    | inv_left => (fun args => mul' (inv' (args Only)) (args Only))
    | inv_right => (fun args => mul' (args Only) (inv' (args Only)))
  end.

(* The right-hand sides of group equations *)
Definition Group_rhs (A : OpAlgebra GroupOp) (e : Group_equation) :
  (Group_eq_arity e → A) → A :=
  match e with
    | assoc => (fun args => mul' (mul' (args One) (args Two)) (args Three))
    | unit_left => (fun args => args Only)
    | unit_right => (fun args => args Only)
    | inv_left => (fun args => one')
    | inv_right => (fun args => one')
  end.

(* The signature for group equations, we need to show they're natural. *)
Definition GroupEq : EqSignature GroupOp.
Proof.
  refine {|
    eq := Group_equation ;
    eq_arity := Group_eq_arity ;
    lhs := Group_lhs ;
    rhs := Group_rhs
  |}.
  (* A bit of Coq magic does the job. *)
  - intros A B f [] args ;
    (unfold Group_lhs, Group_rhs ;
      repeat (unfold one', mul', inv';
              rewrite op_commute; f_equal; apply functional_extensionality;
              intros []; try reflexivity)).
  - intros A B f [] args ;
    (unfold Group_lhs, Group_rhs ;
      repeat (unfold one', mul', inv';
              rewrite op_commute; f_equal; apply functional_extensionality;
              intros []; try reflexivity)).
    + reflexivity.
    + reflexivity.
Defined.

(* And finally, we can define what a group is. *)
Definition Group := Algebra GroupOp GroupEq.

Section BoolGroup.

(* Let us show that the booleans form a group with the xor as the group operation. *)

Definition xor (x y : bool) :=
  match x with
    | false => y
    | true => (match y with false => true | true => false end)
  end.

(* We first define the structure without equations. *)
Definition BoolOp : OpAlgebra GroupOp := {|
  carrier := bool ;
   op := (fun (o : operation GroupOp) => match o with
                                           | one => (fun args => false)
                                           | mul => (fun args => xor (args Fst) (args Snd))
                                           | inv => (fun args => args Only)
                                         end)
|}.

(** Then we define the group Bool by showing that BoolOp satisfies the group equations. *)
Definition Bool : Group.
Proof.
  exists BoolOp.
  intros [] args ; simpl; try (destruct (args Only) ; reflexivity).
  destruct (args One); destruct (args Two); destruct (args Three); reflexivity.
Defined.

End BoolGroup.

Section Product.

(* Let us do a bit of general theory by showing that the algebras for a given signature
   are closed under products. *)

(* The product of an I-indexed family of operation algebras. *)
Definition ProductOp {S : OpSignature} {I : Type} (A : I → OpAlgebra S) := {|
  carrier := ∀ i, A i ;
  op := (fun (o : operation S) args i => op (A i) o (fun j => args j i))
|}.

(* Projections are homomorphisms. *)
Definition Project {S : OpSignature} {I : Type} (A : I → OpAlgebra S) (i : I) :
  AlgHom (ProductOp A) (A i).
Proof.
  exists (fun (x : ProductOp A) => x i).
  reflexivity.
Defined.

(* The product of an I-indexed family og algebras. *)
Definition Product {S : OpSignature} {E : EqSignature S} (I : Type) :
  (I → Algebra S E) → Algebra S E.
Proof.
  intro A.
  exists (ProductOp A).
  intros e args.
  apply functional_extensionality_dep.
  intro i.
  pose (L := lhs_natural _ E _ _ (Project A i) e args); simpl in L.
  rewrite L.
  pose (R := rhs_natural _ E _ _ (Project A i) e args); simpl in R.
  rewrite R.
  apply equations.
Defined.

End Product.

End Examples.

Record Interface := {
  intf    : OpSignature;
  laws    : EqSignature intf;
  algebra : Algebra intf laws
}.

(** A software component maps from algebras required to algebras provided by
    the component, where the signatures of each may be unrelated. It is a true
    algebraic transformer. *)
Definition Component (required provided : Interface) : Type :=
  { f : Interface → Interface & f required = provided }.

#[export] Program Instance Component_Setoid {req prov : Interface} :
  Setoid (Component req prov) := {|
  equiv := fun f g : Component req prov => f = g
|}.

(** Now we may reason about the category of software components, which are
    simply morphisms between algebras, but not necessarily homomorphic. *)

#[export]
Program Instance Comp : Category := {
  obj     := Interface;
  hom     := Component;
  homset  := @Component_Setoid;
  id      := fun x => (fun req => req; reflexivity _);
  compose := fun _ _ _ f g => (fun req => `1 f (`1 g req); _)
}.
Next Obligation.
  destruct f, g; simpl in *.
  now rewrite e0, e.
Defined.
Next Obligation.
  destruct f; simpl in *.
  f_equal.
  simpl_eq.
  now destruct e.
Defined.
Next Obligation.
  destruct f; simpl in *.
  simpl_eq; simpl.
  now destruct e.
Defined.
Next Obligation.
  destruct f, g, h; simpl in *.
  simpl_eq; simpl.
  now destruct e, e0, e1.
Defined.
Next Obligation.
  destruct f, g, h; simpl in *.
  simpl_eq; simpl.
  now destruct e, e0, e1.
Defined.

End UniversalAlgebra.
