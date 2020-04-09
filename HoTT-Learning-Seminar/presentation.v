(*This is a brief and not complete introduction to using HoTT Coq*)
(*We firstly need to import the HoTT module. This is done with the following command*)
Require Import HoTT.

(*Let's prove something very basic*)
Theorem my_first_proof : forall (A : Type), A -> A. (*This is where we name our theorem and define the type*)
Proof.
  intro A. (*We first need to introduce the type A*)
  intro pf_of_A. (*To prove an implication, we assume the antecedent. Via propositions-as-types, this is the same as assuming we have an element of type A, or rather, a proof of A.*)
  exact pf_of_A. (* Our goal was to find a proof of A, which we have. We use the exact command to finish complete this goal.*)
Defined.

Theorem ex2 : forall (A B : Type), A -> (A -> B) -> B.
Proof.
  intros A B.
  intro pf_of_A. (*We introduce a proof of A, then a proof of A -> B.*)
  intro pf_A_imp_B.
  pose (pf_of_B := pf_A_imp_B pf_of_A). (*We use the "pose" command to define new things. This doesn't change the goal. Here, we define a proof of B.*)
  exact pf_of_B.
Defined.

Theorem ex2' : forall (A B : Type), A -> (A -> B) -> B.
Proof.
  intros A B.
  intros pf_A pf_A_imp_B.
  refine (pf_A_imp_B _). (*The "refine" command is used when we know that to prove our goal, it is sufficient to prove something else. As we have that A -> B, to prove B, it is sufficient to prove A. This changes the goal.*)
  exact pf_A.
Defined.


Theorem ex_refine : forall (A B C : Type), A -> (A -> B) -> (B -> C) -> C.
Proof.
  intros A B C.
  intros pf_A pf_A_imp_B pf_B_imp_C.
  refine (pf_B_imp_C _).
  refine (pf_A_imp_B _). (*We can use the refine command multiple times to complete our proof.*)
  exact pf_A.
Defined.

Theorem ex_refine2 : forall (A B C : Type), A -> (A -> B) -> (A -> B -> C) -> C.
Proof.
  intros A B C.
  intros pf_A pf_A_imp_B pf_A_imp_B_imp_C. 
  refine (pf_A_imp_B_imp_C _ _). (*The "refine" command works as a function. To prove using A->B->C, we need two proofs: one of A and one of B. This is why we have two _ marks.*)
  + exact pf_A. (*The + is a bullet. We use it to split cases up. We can have different levels of cases, each using a differenet bullet symbol: +-*.*)
  + refine (pf_A_imp_B _).
    exact pf_A.
Defined.

Theorem triple_neg : forall (A : Type), not (not (not A)) -> not A.
Proof.
  intros A. unfold not. (*unfold is used to expand terms we are proving or have already.*)
  intro foo1.
  intro pf_A.
  refine(foo1 _).
     intro pf_not_A.
     exact (pf_not_A pf_A).
Defined.

Proposition jarl1 : forall (A : Type), A -> not (not A).
Proof.
 intros A.
 intro pf_A.
 unfold not.
 intro pf_not_A.
 exact (pf_not_A pf_A).
Defined.

Proposition jarl2 : forall (A : Type), A -> not (not A).
Proof.
  intro A.
  exact (fun a : A => fun g : A -> Empty => g a). (*The is used for lambda notation. *)
Defined.

Theorem absurd : forall (A B : Type), A -> not A -> B.
Proof.
  intros A B.
  intro pf_A. intro pf_not_A.
  pose (pf_of_False := pf_not_A pf_A).
  case pf_of_False. (*We can use "case" to prove any goal from a falsehood. *)
Defined.

Theorem left_or : forall (A B : Type), A -> A + B. (*Following the notatio from the book, we use "+"" to mean "or" We can also use "\/". *)
Proof.
  intros A B.
  intros pf_A.
  pose (pf_A_or_B := inl pf_A : A + B). (*We need to specify the output type here as it can't be determined from the given information.*)
  exact pf_A_or_B.
Defined.

Theorem right_or : forall (A B : Type), B -> A + B.
Proof.
  intros A B.
  intros pf_B.
  pose (pf_A_or_B := inr pf_B : A + B).
  exact pf_A_or_B.
Defined.

Theorem or_commutes1 : forall (A B : Type), A + B -> B + A.
Proof.
  intros A B.
  intro pf_A_or_B.
  case pf_A_or_B. (*We use case again - it perfoms a case analysis on the given term to help prove the goal.*)
  + intro pf_A. exact (right_or B A pf_A).
  + intro pf_B. exact (left_or B A pf_B). (*Previous theorems can be used and referred to in other proofs*)
Defined.

Theorem or_commutes2 : forall (A B : Type), A + B -> B + A.
Proof.
  intros A B.
  intro pf_A_or_B.
  destruct pf_A_or_B.
  + exact (right_or B A a).
  + exact (left_or B A b).
Defined.

Theorem both_and : forall (A B : Type), A -> B -> prod A B.
Proof.
  intros A B.
  intros a b.
  refine (pair _ _).
  + exact a.
  + exact b.
Defined.

Theorem and_commutes1 : forall (A B : Type), A * B -> B * A.
Proof.
  intros A B.
  intro pf_A_and_B.
  case pf_A_and_B.
  intros a b.
  exact (pair b a).
Defined.

Theorem and_commutes2 : forall (A B : Type), A * B -> B * A.
Proof.
  intros A B.
  intro pf_A_and_B.
  destruct pf_A_and_B as [pf_A pf_B].
  refine (pair _ _).
  + exact pf_B.
  + exact pf_A.
Defined.

(*Pi types*)

Theorem triv : forall (A : Type), forall (x : A), x = x.
Proof.
  intros A x.
  reflexivity.
Defined.

(*Sigma types*)

Theorem nat_eq_is_serial : forall (n : nat), exists (m : nat), n = m.
Proof.
  intros n.
  exists n.
  reflexivity.
Defined.

Definition serial_eq (A : Type) : Type := forall (a : A), exists (b : A), a = b.


Theorem eq_is_serial : forall (A : Type), serial_eq A.
Proof.
  intros A.
  unfold serial_eq.
  intro a.
  exists a. reflexivity.
Defined.

Theorem sigma_proj : forall (A : Type) (P : A -> Type), (exists (x : A), P x) -> A.
Proof.
  intros A P.
  intro pf_sigma_P.
  destruct pf_sigma_P as [x G].
  exact x.
Defined.

(*Identity Types*)

Theorem id_is_refl : forall (A : Type) (x : A), x = x.
Proof.
  intros A x.
  reflexivity.
Defined.

Theorem id_is_sym : forall (A : Type) (x y : A), x=y -> y=x.
Proof.
  intros A x y.
  intro p.
  induction p.
  reflexivity.
Defined.

Theorem id_is_transitive : forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros A x y z.
  intros p q.
  induction p.
  induction q.
  reflexivity.
Defined.

Theorem transport' : forall (A : Type) (P : A -> Type) (x y : A), x = y -> P x = P y.
Proof.
  intros A P x y.
  intro p.
  induction p.
  reflexivity.
Defined.

Theorem pathlift : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof.
  intros A B f x y.
  intro p.
  induction p.
  reflexivity.
Defined.



Theorem ac : forall (A B : Type) (R : A -> B -> Type), (forall x : A, exists y : B, R x y) -> (exists (f : A -> B), forall (x : A), R x (f x)).
Proof.
  intros A B R.
  intro H.
  pose (f := fun x : A => pr1(H x)).
  exists f.
  pose (g := fun x : A => pr2(H x)).
  exact g.
Defined.


Inductive Nats : Type :=
| O : Nats
| S : Nats -> Nats.

Fixpoint plus (n m : Nats) : Nats :=
  match (n) with
  | O => m
  | S p => S(p + m)
          end
where "p + m" := (plus p m).


Print concat_p1.
Print transport.

Lemma foo : forall (n : Nats), plus O n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Defined.

Lemma foo' : forall (n : Nats), plus n O = n.
Proof.
  intros n.
  induction n.
  + reflexivity.
  + simpl.
    rewrite -> IHn.
    reflexivity.
Defined.

Lemma plus_assoc : forall (n m k : Nats), (n + m) + k = n + (m + k).
Proof.
  intros n m k.
  induction n.
  + simpl.
    reflexivity.
  + induction m.
    - simpl.
      rewrite <- IHn. reflexivity.
    - simpl. induction k.
      * simpl. rewrite <- IHn. reflexivity.
      * 
