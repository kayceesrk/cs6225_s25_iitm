Require Import Frap.

Set Implicit Arguments.


Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition pid (* process id *) := nat.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Send (receiver : pid) (e : arith)
| Recv (sender : pid) (x : var).

Definition valuation := fmap var nat.

Definition state := list (pid * valuation * cmd).

(* Here are some notations for the language, which again we won't really
 * explain. *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Notation "p ! e" := (Send p e%arith) (at level 75).
Notation "p ? x" := (Recv p x) (at level 75). 
Infix ";;" := Sequence (at level 76, right associativity). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

Definition terminated (s : state) := False (* fill in *).

Inductive context := (* fill in *).

Inductive plug : context -> cmd -> cmd -> Prop := (* fill in *).

(* 5 points *)
Inductive step0 : valuation * cmd -> valuation * cmd -> Prop := (* fill in *).

(* 5 points *)
Inductive step : state -> state -> Prop := (* fill in *).


Definition ex1 : state := [(0, $0, 1 ! 42); (1, $0, 0 ? "x")].

(* 5 points *)
Theorem thm1 : exists v l, step^* ex1 ((1,v,Skip)::l) 
                                 /\ v $? "x" = Some 42.
Proof.
Admitted.


(* Lone sender blocks : 2.5 points *)
Theorem thm2 : forall pid1 v pid2 e st, 
  step ^* [(pid1, v, pid2 ! e)] st -> terminated st -> False.
Proof.
Admitted.

(* Lone receiver blocks : 2.5 points *)
Theorem thm3 : forall pid1 v pid2 x st,
  step ^* [(pid1, v, pid2 ? x)] st -> terminated st -> False.
Proof.
Admitted.

Example ex4 : state := [(0, $0, 1 ! 42;; 
                                2 ? "x");
                        (1, $0, 0 ? "x";;
                                2 ! "x" + 1);
                        (2, $0, 1 ? "x";;
                                0 ! "x" + 1)].

(* 5 points *)
Theorem thm4 : exists v l, 
  step ^* ex4 ((0, v, Skip)::l) /\ v $? "x" = Some 44.
Proof.
Admitted. 

Definition producer (recv_pid : nat) (num_msgs : nat) :=
  "i" <- num_msgs;;
  while "i" loop
    recv_pid ! "i";;
    "i" <- "i" - 1
  done;;
  recv_pid ! 0.
  
Definition consumer (send_pid : nat) :=
  "again" <- 1;;
  "sum" <- 0;;
  while "again" loop
    send_pid ? "again";;
    "sum" <-  "sum" + 2 * "again"
  done.

(* 5 points *)
Theorem thm5 : exists v l, 
  step ^* [(0, $0, producer 1 2); (1, $0, consumer 0)] ((1,v,Skip)::l) 
        /\ v $? "sum" = Some 6.
Proof.
Admitted.


(* Challenge problem : Additional 5% of course grade! *)
Theorem thm6 : forall n, exists v l,
  step ^* [(0, $0, producer 1 n); (1, $0, consumer 0)] ((1,v,Skip)::l) 
        /\ v $? "sum" = Some (n * (n + 1)).
Proof.
Admitted.