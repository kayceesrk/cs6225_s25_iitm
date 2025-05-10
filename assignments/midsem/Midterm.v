(** CS6225 Spring 2025: Programs and proofs -- Mid Term *)

(***************************************
 ** Instructions
 ***************************************

   This is a take home exam, with 24 hours for the exam. Strictly no late
   submissions allowed. Submit your solutions through course moodle.

   Completed solutions should not have any [Abort]ed proofs. If there are, they
   will get [0] points. There are a few lemmas and theorems for which the proof
   ends with [Admitted]. For example, see [fib_succ_add] and
   [fib_fib_tail_rec']. Those are the only ones for which you may leave the
   proof as admitted and use it in the subsequent theorems ([fib_ok] for
   example). Your solution will not have any other [Admitted] proofs. Any other
   use of [Admitted] proofs will get [0] points. *)

Require Import Frap MidtermSig.

(***************************************
 ** Swivel
 ***************************************)

Inductive tree :=
  | Leaf
  | Node (v : nat) (lt rt : tree).
  
Fixpoint rightmost (tr: tree) : option nat :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    match rt with
    | Leaf => Some v
    | _ => rightmost rt
    end
  end.
  
Fixpoint leftmost (tr : tree) : option nat := None. (* Remove [None] and fill in *)
(* 3 points *)
  
Fixpoint swivel tr :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt => Node v (swivel rt) (swivel lt)
  end.
  
Theorem swivel_ok : forall tr, 
  leftmost tr = rightmost (swivel tr).
(* 5 points *)
Proof.
Abort.

(***************************************
 ** Fibonacci Sequence
 ***************************************)

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n'' + fib n'
            end
  end.

Fixpoint fib_tail_rec' n a b :=
  match n with
  | 0 => a
  | S n' => fib_tail_rec' n' b (a+b)
  end.

Definition fib_tail_rec n := n + 0.
(* Remove [n + 0] and fill in correct definition *)
(* 2 points *)

Example ex1: fib 10 = 89.
Proof.
  auto.
Qed.

Example ex2: fib_tail_rec 10 = 89.
Proof.
  auto.
Abort.

Lemma fib_succ_add: forall n,
  fib n + fib (n+1) = fib(n+2).
(* 5 points *)
Proof.
  (* FILL IN *)
Admitted.

Lemma fib_fib_tail_rec': forall n k,
  fib_tail_rec' n (fib k) (fib (k+1)) = fib (k+n).
(* 5 points *)
Proof.
  (* FILL IN *)
Admitted.

Theorem fib_ok : forall n, fib n = fib_tail_rec n.
(* 5 points *)
Proof.
  (* FILL IN *)
Abort.

(***************************************
 ** List.rev is involutive
 **************************************)

Require Import List.
Import ListNotations.

Theorem rev_involutive : forall (A:Type) (l : list A), rev (rev l) = l.
(* 5 points *)
Proof.
Abort.

(***************************************
 ** Insertion sort
 ***************************************
 
 
  We will define insertion sort and prove it right. Consider the following 
  idea. Given the input list l = [4;5;1;3], sorting proceeds like this:

  Using an auxilliary list [sorted]:

  l=[4;5;1;3] aux=[]
  l=[5;1;3]   aux=[4]
  l=[1;3]     aux=[4;5]
  l=[3]       aux=[1;4;5]
  l=[]        aux=[1;3;4;5]
  
  Observe that [aux] is always sorted. The idea is that, at each step, 
  we take one element from [l] and insert into [aux] at the right position 
  so that [aux] remains sorted. When [l] is empty, [aux] is the sorted version 
  of the input list [l].
  
  In a typical insertion sort, you can do binary search on [aux] list and 
  insert, leading to O(n log(n)) running time. We will just do a linear search
  through [aux] to find the correct position.

  We will use the comparison function [compare] that you have seen in the
  assignment. *)

Require Import OrdersFacts.

Check compare.
Print comparison.

(* In order to prove facts, you will need the definitions from the following. *)

Include (OrderedTypeFacts MidtermSig).
Include (OrderedTypeTest MidtermSig).

(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* FYI, our solution only uses the following three facts, but you may use other 
   facts. *)

Check compare_gt_iff.
Check compare_lt_iff.
Check compare_eq_iff.

(* You will need to define a function [sort] that returns a sorted version 
   of the input list based on the insertion sorting algorithm above: *)
  
Definition sort (l : list t) : list t := l. 
(* Remove [l] and fill in correct defintion. *)
(* 5 points *)

(* In order to do the proof, we will define an inductive type called [sorted] 
   that captures that 
  
    (1) An empty list is sorted.
    (2) A singleton list is sorted.
    (3) Given a list [l = x::y::t], in order for [l] to be sorted, it better 
        be the case that [lt x y \/ eq x y] and [sorted (y::t)].
  
   Check the definition of [lt] and [eq] below:
*)

Check lt.
Check eq.

Inductive sorted : list t -> Prop := . (* FILL IN *)
(* 5 points *)

(* Prove the following theorem: the result of the [sort] function 
   returns a [sorted] list. *)

Theorem sort_ok : forall l, sorted (sort l).
(* 10 points *)
Proof.
Abort.

(* Of course, one also needs to prove that the sorted list is a permutation of 
   the original list. For this, we need to talk about list membership. In Coq, 
   we use `In` construct to describe list membership. For example, *)

Theorem in_list : In 3 [1;2;3].
Proof.
  simplify; equality.
Qed.

Theorem not_in_list : In 4 [1;2;3] -> False.
Proof.
  simplify; equality.
Qed.

(* Now to the theorem *)
Theorem sort_is_permutation : forall l e, In e l -> In e (sort l).
(* 20 points *)
Proof.
Abort.

(* You may need some intermediate lemmas based on the intermediate functions 
   that you may have written down. *)