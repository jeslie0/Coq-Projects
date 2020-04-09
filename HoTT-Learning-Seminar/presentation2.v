Require Import HoTT.
Open Scope type_scope.

Theorem ac : forall (A B : Type) (R : A -> B -> Type), (forall x : A, exists y : B, R x y) -> (exists (f : A -> B), forall (x : A), R x (f x)).
Proof.
  intros A B R.
  intro H.
  pose (f := fun x : A => pr1(H x)).
  exists f.
  pose (g := fun x : A => pr2(H x)).
  exact g.
Defined.

Definition isProp (P : Type) : Type := forall (x y : P), x = y.

Definition isSet (A : Type) : Type := forall (x y : A), isProp (x = y).

Definition isContr (A : Type) : Type := exists (a : A), forall (x : A), a = x.

Definition homotopy {A B : Type} (f g : A -> B) : Type := forall (x : A), (f x = g x).

Definition qinv {A B : Type} (f : A -> B) : Type := exists (g : B -> A), (homotopy (f o g) idmap) * (homotopy (g o f) idmap).

Definition isEquiv {A B : Type} (f : A -> B) : Type := (exists g:B -> A, homotopy (f o g) (idmap : B -> B)) * (exists h: B -> A, homotopy (h o f) (idmap : A -> A)).

Definition equiv (A B : Type) : Type := exists f:A -> B, isEquiv f.
Notation "A ~ B" := (equiv A B) (at level 80, no associativity).

Definition LEM : Type := forall (A : Type), isProp A -> (A + ~A).

Definition DN : Type := forall (A : Type), isProp A -> ((~(~A)) -> A).

Lemma qinv_to_isequiv : forall {A B : Type} (f : A -> B), qinv f -> isEquiv f.
Proof.
  intros A B f H.
  unfold isEquiv.
  unfold qinv in H.
  destruct H as [g G].
  destruct G as [a b].
  split.
  + exists g.
    unfold homotopy.
    intros x.
    exact (a x).
  + exists g.
    intros x.
    exact (b x).
Defined.


Lemma lem3_6i `{Funext} : forall (A B : Type), isProp B -> isProp (A -> B).
Proof.
  intros A B H'.
  unfold isProp.
  intros f g.
  unfold isProp in H'.
  refine (path_arrow f g _).
  intros x.
  exact (H' (f x) (g x)).
Defined.

Lemma lem2_6ii : isProp Empty.
Proof.
  intros x y.
  induction x.
Defined.

Lemma not_A_isProp`{Funext} : forall A : Type, isProp (~ A).
Proof.
  intros A.
  exact(lem3_6i A Empty lem2_6ii).
Defined.

Theorem ex3_6 `{Funext} : forall (A : Type), isProp A -> isProp (A + ~ A).
Proof.
  intros A F x y.
  destruct x.
  + destruct y.
    - induction (F a a0).
      reflexivity.
    - contradiction (n a).
  + destruct y.
    - contradiction (n a).
    - unfold isProp in F.
      pose (not_A := not_A_isProp A).
      pose (foo := not_A n n0).
      exact (ap inr foo).
Defined.

Theorem lem_implies_dn : LEM -> DN.
Proof.
  intros lem A H.
  pose (a_not_a := lem A H). 
  destruct a_not_a as [x | y].
  + intro not_not_A.
    exact x.
  + intro not_not_A.
    pose (cont := not_not_A y).
    contradiction.
Defined.


Theorem dn_implies_lem `{Funext}: DN -> LEM.
Proof.
  intros dn A H'.
  pose (J := ex3_6 A H').
  pose (C := dn (A + ~A) J).
  pose (foo :=(fun g : ~ (A + ~ A) => g (inr (fun a:A => g (inl a))))).
  pose (foo' := C foo).
  exact foo'.
Defined.


Theorem thm2_8_1 `{Funext} `{Univalence} : forall (x y : Unit), (x = y) = Unit.
Proof.
  pose (g := (fun (x y : Unit)(p : (x = y)) => match p with
                                               | idpath => tt : Unit
             end)).
  pose (f := (fun (x y : Unit)(s : Unit) => match x, y, s return (x=y) with
                                            | tt, tt, tt => idpath
                                            end)).

  intros x y.
  apply equiv_path_universe.
  apply (equiv_adjointify (g x y) (f x y)).
  + induction x. induction y. intro x. induction x. simpl. reflexivity.
  + induction x. induction y. intro y. induction y. simpl. reflexivity.
Defined.
