Require Import HoTT.

Definition homotopy {A B : Type} (f g : A -> B) : Type := forall x : A, f x = g x.
Definition isEquiv {A B : Type} (f : A -> B): Type := exists (g : B -> A), (homotopy (g o f) (idmap)) /\ (homotopy (idmap) (f o g)).
Definition Equiv (A B : Type) : Type := exists (f : A -> B), isEquiv f.
Axiom Univalence : forall (A B : Type), Equiv (Equiv A B) (A = B).

Module Export Circle.
  Private Inductive circle : Type := base : circle.
  Axiom loop : base = base.
  Definition circle_dep_ind (P : circle -> Type) (b : P base) (p : transport P loop b = b) : forall x : circle, P x :=
  fun y => (match y with
         | base => fun _ => b
         end) p.
  Axiom circle_dep_comp : forall (P : circle -> Type) (b : P base) (p : transport P loop b = b), apD (circle_dep_ind P b p) loop = p.
  Definition circle_ind (B : Type) (b : B) (l : b = b): circle -> B :=
    fun y => (match y with
           | base => fun _ => b
          end) l.
  Axiom circle_comp : forall (B : Type) (b : B) (l : b = b), ap (circle_ind B b l) loop = l.
End Circle.

Module Export Circle'.
Private Inductive circle' : Type := east : circle' | west : circle'.
Axiom p1 : east = west.
Axiom p2 : west = east.
Definition circle'_dep_ind (P : circle' -> Type) (a : P east) (b : P west) (s : transport P p1 a = b) (t : transport P p2 b = a) : forall x : circle', P x := fun y => (match y with
                                                                                                                         | east => a
                                                                                                                         | west => b
                                                                                                                             end).

Axiom circle'comp1 : forall (P : circle' -> Type) (a : P east) (b : P west) (s : transport P p1 a = b) (t : transport P p2 b = a), apD (circle'_dep_ind P a b s t) p1 = s.


Axiom circle'comp2 : forall (P : circle' -> Type) (a : P east) (b : P west) (s : transport P p1 a = b) (t : transport P p2 b = a), apD (circle'_dep_ind P a b s t) p2 = t.

Definition circle'_ind (B : Type) (a : B) (b : B) (l : a = b) (m : b = a): circle' -> B :=
  fun y : circle' => (match y with
                  | east => a
                  | west => b
                             end).

Axiom circle'_comp1 : forall (B : Type) (a : B) (b : B) (l : a = b) (m : b = a), ap (circle'_ind B a b l m) p1 = l.
Axiom circle'_comp2 : forall (B : Type) (a : B) (b : B) (l : a = b) (m : b = a), ap (circle'_ind B a b l m) p2 = m.
End Circle'.

Theorem concat_id : forall {A : Type} {a b : A} (p : a = b), 1 @ p = p.
  intros A a b p.
  induction p.
  reflexivity.
Defined.

Lemma lem0 : forall {A B C : Type} {a b : A} (f : A -> B) (g :B -> C) (p : a = b), ap (g o f) p = ap g (ap f p).
Proof.
  intros A B C a b f g p.
  induction p. simpl.
  reflexivity.
Defined.


Theorem thm2_11_3 : forall {A B : Type} {a a' : A} (f g : A -> B) (p : a = a') (q : f a = g a), transport (fun x : A => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  intros A B a a' f g p q.
  induction p. simpl.
  induction q.
  reflexivity.
Defined.


Goal forall (A : Type) (a : A) (P : A -> Type) (y : P a), exists (x : A), P x.
Proof.
  intros A a P y.
  refine (ex_intro _ a _).
  exact y.
Defined.

Lemma f : circle -> circle'.
Proof.
  apply (circle_ind circle' east).
  exact (p1 @ p2).
Defined.

Lemma g : circle' -> circle.
Proof.
  apply (circle'_ind circle base base).
  + exact loop.
  + reflexivity.
Defined.

Lemma lem1 : ap g p1 = loop.
Proof.
  apply circle'_comp1.
Defined.

Lemma lem2  : ap g p2 = idpath.
Proof.
  apply circle'_comp2.
Defined.

Lemma lem3 : ap f loop = p1 @ p2.
Proof.
  apply circle_comp.
Defined.

Lemma lem4 : forall {A : Type} {a b c : A} (p : a = b) (q : b = c), (p@q)^ = q^ @ p^.
Proof.
  intros A a b c p q.
  induction p.
  induction q.
  reflexivity.
Defined.

Lemma lem5 : f (g east) = east.
Proof.
  simpl.
  reflexivity.
Defined.

Lemma lem6 : f (g west) = west.
Proof.
  simpl.
  exact p1.
Defined.

Lemma lem7 : forall {A: Type} {a b : A} (p : a = b), ap idmap p = p.
Proof.
  intros A a b p.
  induction p.
  simpl. reflexivity.
Defined.


Lemma lem8 : forall {A : Type} {a b : A} (p : a = b), p @ idpath = p.
Proof.
  intros A a b p.
  induction p.
  reflexivity.
Defined.

Lemma lem8' : forall {A : Type} {a b : A} (p : a = b), idpath @ p = p.
Proof.
  intros A a b p.
  induction p.
  reflexivity.
Defined.

Lemma lem9 : forall {A : Type} {a b c d : A} (p : a = b) (q : b = c) (r : c = d), (p @ q) @ r = p @ (q @ r).
Proof.
  intros A a b c d p q r.
  induction p. induction q. induction r.
  reflexivity.
Defined.

Lemma lem10 : forall {A : Type} {a b : A} (p : a = b), p^ @ p = idpath.
Proof.
  intros A a b p.
  induction p.
  reflexivity.
Defined.

Lemma lem11 : (ap (f o g) p1)^ @ idpath @ (ap idmap p1) = p2^.
Proof.
  rewrite (lem0 g f p1).
  rewrite lem1.
  rewrite lem3.
  rewrite (lem4 p1 p2). 
  rewrite (lem7 p1).
  rewrite (lem8 (p2^ @ p1^)).
  rewrite (lem9 p2^ p1^ p1).
  rewrite (lem10 p1).
  rewrite (lem8 p2^).
  reflexivity.
Defined.

Lemma lem12 : forall x : circle',  f (g x) = x.
Proof.
  apply (circle'_dep_ind (fun x : circle' => f (g x) = x) (idpath) (p2^)).
  + rewrite <- lem11.
    exact (thm2_11_3 (f o g) (idmap) p1 idpath).
  + rewrite (thm2_11_3 (f o g) idmap p2 p2^).
    rewrite (lem7 p2).
    rewrite (lem0 g f p2).
    rewrite lem2. simpl.
    rewrite lem8'.
    rewrite (lem10 p2).
    reflexivity.
Defined.

Lemma lem13 : forall {A B: Type} {x y z : A} (f : A -> B) (p : x = y) (q : y = z), ap f (p @ q) = (ap f p) @ (ap f q).
Proof.
  intros A B x y z f p q.
  induction p. induction q.
  reflexivity.
Defined.

Lemma lem14 : forall x : circle, g (f x) = x.
Proof.
  apply (circle_dep_ind (fun x : circle => g (f x) = x) idpath).
  rewrite (thm2_11_3 (g o f) idmap loop idpath).
  rewrite (lem7 loop).
  rewrite (lem0 f g loop).
  rewrite lem3.
  rewrite (lem13 g p1 p2).
  rewrite lem1.
  rewrite lem2.
  repeat rewrite lem8.
  rewrite lem10.
  reflexivity.
Defined.

Lemma f_isEquiv : isEquiv f.
  exists g.
  split.
  + exact lem14.
  + unfold homotopy. intro x.
    symmetry.
    exact (lem12 x).
Defined.

Theorem circles_are_equal : circle = circle'.
Proof.
  apply Univalence.
  exists f.
  exact f_isEquiv.
Defined.
