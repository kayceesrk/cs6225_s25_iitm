Require Import List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import Frap.

Fixpoint odds {A : Type} (lst : list A) : list A :=
  match lst with
  | nil => nil
  | cons h1 nil => cons h1 nil
  | cons h1 (cons h2 t) => cons h1 (odds t)
  end.

Check odds.

Compute odds [].
Compute odds [1;2;3;4;5].

Fixpoint length {A : Type} (lst : list A) : nat :=
  match lst with
  | nil => 0
  | cons _ t => 1 + length t
  end.

Check length.

Compute length [].
Compute length [1;2;3;4].

Lemma len_cons: forall {A:Type} (a:A) (lst: list A), 
  length (a::lst) = 1 + length lst.
Proof.
  intros.
  trivial.
Qed.

Lemma lem2 : forall {A:Type} (a b : A) (lst: list A), 
  length (odds (a::b::lst)) = 1 + length (odds lst).
Proof.
  intros.
  simpl. trivial.
Qed.


Theorem odds_odd_length: 
  forall A : Type, forall n, forall lst: list A, forall a, 
    1 + length lst = 2 * n -> 
    length (odds lst) = n ->
    length (odds (a::lst)) = n.
Proof.
Admitted.

Theorem odds_even_length: 
  forall A : Type, forall lst: list A, forall a, forall n,
    length lst = 2 * n -> 
    length (odds lst) = n ->
    length (odds (a::lst)) = n + 1.
Proof.
Admitted.

Lemma lem1: forall {A:Type} (a:A) (lst:list A) n,  
   1 + length (a :: lst) = 2 * n -> 
   length lst = 2 * (n - 1).
Proof.
  intros.
  cases lst.
  simplify. linear_arithmetic.
  simplify. linear_arithmetic.
Qed.

Theorem odds_length_half:
forall A : Type, forall lst: list A, forall n, 
  (length lst = 2 * n -> length (odds lst) = n) /\
  (1 + length lst = 2 * n -> length (odds lst) = n).
Proof.
  intros A lst.
  induction lst.
  - split; destruct n; simpl; trivial. discriminate. intros. linear_arithmetic. 
  - split; intros. 
    + specialize (IHlst n). destruct IHlst; intros.
      eapply odds_odd_length in H1. eassumption. assumption. assumption.
    + assert (n > 0). simpl in H. linear_arithmetic.
      specialize (IHlst (n - 1)). destruct IHlst. apply lem1 in H.
      apply (odds_even_length A lst a (n - 1)) in H1. linear_arithmetic.
      assumption. assumption.
Qed.