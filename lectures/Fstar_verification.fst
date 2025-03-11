module Fstar_verification

open FStar.Mul
module List = FStar.List.Tot.Base

(** There are two approaches to verification in F*

    (1) Intrinsically at definition time
    (2) Extrinsically through SMT-backed lemmas

    We have already seen several examples of intrinsic verification.
*)

val factorial : nat -> Tot nat              (* type nat = x:int{x >= 0} *)
let rec factorial n =
  if n = 0 then 1 else n * factorial (n-1)

(* We can also equivalently write pre- and post-conditions for this *)

val factorial2 : x: int -> Pure int (requires (x >= 0))
                                    (ensures (fun y -> y >= 0))
let rec factorial2 n =
  if n = 0 then 1 else n * factorial2 (n-1)

(* In fact, [Tot] is essentially just an abbreviation:

   [Tot t = Pure t (requires True) (ensures (fun _ -> True))]

   Similarly, [Dv] is just an abbreviation for:

   [Dv t = Div t (requires True) (ensures (fun _ -> True))]

   Also, requires and ensures are there only for readability. You can drop them
   if you want.
*)

val factorial3 : x : int -> Pure int (x >= 0) (fun y -> y >= 0)
let rec factorial3 n =
  if n = 0 then 1 else n * factorial3 (n-1)

(******************************************************************************)

(** A high-level view of types in F*

    You can view types in F* as belonging to two "kinds"

    * Value types (V) -- int, int list, ...
    * Computation types (C) -- Tot t, Dv t, ...

    Types can also be refined:

    * Refined value types -- x:t{p}
    * Refined computation types
      + Pure t pre post
      + Div t pre post

    Dependent functions are of the form

    [x0:t0 -> ... -> xn:tn{x0...xn-1} -> C ]

    where the notation {x0...xn-1} says that the variables x1 to xn-1 may appear
    free in the refinement.
*)

(******************************************************************************)

(* Intrinsically verifying append *)

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | _::ls -> 1 + length ls


val append : l1:list 'a -> l2:list 'a -> l3:list 'a{length l3 = length l1 + length l2}
let rec append l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x::(append xs l2)

(******************************************************************************)

(* Extrinsically verifying append

   We can under specify the type of [append] and verify the fact about length as
   a separate lemma.

*)

val append2 : list 'a -> list 'a -> list 'a
let rec append2 l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x::(append2 xs l2)

val append_len :
  l1:list 'a -> l2:list 'a ->
  Pure unit (requires True)
            (ensures (fun _ -> length (append2 l1 l2) = length l1 + length l2))
let rec append_len l1 l2 =
  match l1 with
  | [] -> ()
  (* To show: length (append2 [] l2) = length [] + length l2 *)
  (* Still to show after simplification: length l2 = 0 + length l2 *)
  (* Discharged through SMT Solver: v = 0 + v *)

  (* Proof Engineering *)
  (* Use assertion to verify the conditions that hold inside a branch *)

  (*
     ; assert (length (append2 l1 l2) = length l2)
     ; assert (length l1 + length l2 = length l2)
   *)
  //STOPPED HERE 17/02
  | x::xs -> (* Inductive Case *)

  (* To show: len (append2 (x::xs) l2) = length (x::xs) + length l2 *)
  (* Simplify: len (x::append2 xs l2) = length (x::xs) + length l2 *)
  (* Simplify: 1 + len (append2 xs l2) = (1 + length xs) + length l2 *)

  append_len xs l2
  (* Know recursive call's postcondition: length (append2 xs l2) = length xs + length l2  *)

  (*     length (append2 xs l2) = length xs + length l2 |=
     1 + length (append2 xs l2) = (1 + length xs) + length l2 *)


























(** Lemma Syntactic Sugar

    Lemma (post) = Pure unit (requires True) (ensures (fun _ -> post))
    Lemma (pre) (post) = Pure unit (requires pre) (ensures (fun _ -> post))

*)

let rec append_len2 (l1 l2 : list 'a) :
  Lemma (length (append2 l1 l2) = length l1 + length l2) =
  match l1 with
  | [] -> ()
  | x::xs -> append_len2 xs l2

(******************************************************************************)

(** Why do we want to use extrinic proofs? *)
(** Some times Lemmas are unavoidable. *)

let snoc l h = l @ [h]

(* [#a] is an implicit argument for the [rev] function. You don't need to
   specify it explicitly when calling the function. But can be optionally
   added. *)
val rev: #a:Type -> list a -> Tot (list a)
let rec rev (#a:Type) l =
  match l with
  | [] -> []
  | hd::tl -> snoc (rev (* #a *) tl) hd

(* We want to show that [forall l. rev(rev l) = l]. But this cannot be directly
   expressed as refinement as F* needs to apply two separate inductions,
   neither of which it can apply *)

(*
val rev2 : #a:Type -> f:(list a -> Tot (list a)){forall l. f(f(l)) == l}
let rev2 (#a:Type) l =
  match l with
  | [] -> []
  | hd::tl -> snoc (rev tl) hd
*)

                                             (* rev ([1;2] @ [3]) = 3::rev [1;2] *)
val rev_snoc: #a:Type -> l:list a -> h:a -> Lemma (rev (snoc l h) == h::rev l)
let rec rev_snoc (#a:Type) l h =
  match l with
  | [] -> ()
    (* rev (snoc [] h) == h::rev [] *)
    (* rev ([] @ [h]) == h::[] *)
    (* rev [h] == [h] *)
    (* rev (h::[]) == [h] *)
    (* snoc (rev []) h == [h] *)
    (* snoc [] h == [h] *)
    (* [] @ [h] == [h] *)
    (* [h] == [h] *)
  | x::xs ->
        rev_snoc xs h;
        assert (rev (snoc xs h) == h::rev xs)
    (* post-condition of recursive call (rec_post): rev (snoc xs h) == h::rev xs *)
    (*                                              rev (xs @ [h])  == h::rev xs *)

    (*  To show: rec_post |= rev (snoc (x::xs) h) == h::rev(x::xs) *)
    (* simplify: rec_post |= rev ((x::xs) @ [h]) == h::(snoc (rev xs) x) *)
    (* simplify: rec_post |= rev (x::(xs @ [h])) == h::((rev xs) @ [x]) *)
    (* simplify: rec_post |= snoc (rev (xs @ [h])) x == h::((rev xs) @ [x]) *)
    (* rewrite using IH: rec_post |= snoc (h::rev xs) x == h::((rev xs) @ [x]) *)
    (* simplify : rec_post |= (h::rev xs) @ [x] == h::((rev xs) @ [x]) *)
    (* simplify : rec_post |= h::(rev xs @ [x]) == h::((rev xs) @ [x]) *)

val rev_involutive: #a:Type -> l:list a -> Lemma (rev (rev l) == l)
let rec rev_involutive (#a:Type) l =
  match l with
  | [] -> ()
  | hd::tl ->
      rev_involutive tl;
      // (1) [rev (rev tl) == tl]
      rev_snoc (rev tl) hd
      // (2) [rev (snoc (rev tl) hd) == hd::(rev (rev tl))]

      // These two facts are enough for Z3 to prove the lemma:
      //   rev (rev (hd :: tl)) == hd::tl   {To Prove}
      //   rev (snoc (rev tl) hd) == hd::tl {By def}
      //   hd::(rev (rev tl)) == hd::tl     {By (2)}
      //   hd::tl == hd::tl                 {By (1)}

(******************************************************************************)

(** More verification

    Let's define membership on list. Unlike OCaml, F* doesn't provide equality
    on every type. This is because not all types have decidable equality (types
    are much richer than OCaml). So in order to write mem we cannot quantify
    over arbitrary types, but only over those with decidable equality. *)

(* [#a:eqtype] is syntactic sugar for [#a:Type{hasEq a}] *)
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd :: tl -> hd = x || mem x tl

val append_mem:  #a:eqtype -> l1:list a -> l2:list a -> x:a
        -> Lemma (mem x (append l1 l2) <==> mem x l1 || mem x l2)
let rec append_mem (#a:eqtype) l1 l2 x =
  match l1 with
  | [] -> ()
  | hd::tl ->
      append_mem tl l2 x
      // (IH) mem x (append tl l2 x) <==> mem x tl || mem x l2
      // To show:   mem x (append (hd::tl) l2) <==> mem x (hd::tl) || mem x l2
      // simplify:  mem x (hd::append tl l2) <==> hd = x || mem x tl || mem x l2
      // simplify:  hd = x || mem x (append tl l2) <==> hd = x || mem x tl || mem x l2
      // Proved by rewriting using IH

(******************************************************************************)

(** Tail recursive factorial [recall from Coq Induction lecture]*)

val fact_tail_rec' : n:nat -> acc:nat -> r:nat{r = factorial n * acc}
let rec fact_tail_rec' n acc =
  if n = 0 then acc
  else fact_tail_rec' (n-1) (n * acc)

let fact_tail_rec n = fact_tail_rec' n 1

val fact_same : n:nat -> Lemma (ensures (factorial n = fact_tail_rec n))
let rec fact_same n =
  if n = 0 then ()
  else fact_same (n-1)

(* STOPPED HERE 19/02 *)

(******************************************************************************)

(** Insertion Sort

    Let us implement and verify an insertion sort algorithm.

    Section 6.1.3 in https://www.fstar-lang.org/tutorial/
*)

val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(*
val insert_sorted :
  a:int ->
  l:list int{sorted l} ->
  Tot (r:list int{sorted r /\ (forall x. mem x r <==> x==a \/ mem x l)})
let rec insert_sorted a l = match l with
  | [] -> [a]
  | x::xs ->
     if a <= x then
       a::l
     else
       x::insert_sorted a xs
*)

(*
val insert_sorted :
  a:int ->
  l:list int{sorted l} ->
  Tot (r:list int{sorted r /\ (forall x. mem x r <==> x=a \/ mem x l)})
let rec insert_sorted a l = match l with
  | [] -> [a]
  | x::xs ->
     if a <= x then
       a::l
     else
       let stl = insert_sorted a xs in
       assert (forall y. mem y stl <==> y = a \/ mem y xs);
       assert (sorted stl);
       assert (a > x);
       let r = x::stl in
       assert (forall x. mem x r <==> x = a \/ mem x l);
       //assert (sorted r);
       r
*)

(* admit ()
   admitP (P1) *)

(* Surprisingly, from the definition of [sorted], we don't automatically get
   the proof that

   [sorted (x::xs) ==> (forall y. mem y xs ==> x <= y)]
*)

(*
val sorted_smaller_lemma:
  x:int ->
  xs:list int ->
  Lemma (requires (sorted (x::xs)))
        (ensures (forall y. mem y xs ==> x <= y))
let sorted_smaller_lemma x xs = ()
*)

(*
val insert_sorted_ :
  a:int ->
  l:list int{sorted l} ->
  Tot (r:list int{sorted r /\ (forall x. mem x r <==> x=a \/ mem x l)})
let rec insert_sorted_ a l = match l with
  | [] -> [a]
  | x::xs ->
     if a <= x then
       a::l
     else
       let stl = insert_sorted_ a xs in
       assert (forall y. mem y stl <==> y = a \/ mem y xs);
       assert (sorted stl);
       assert (a > x);
       let r = x::stl in
       assert (forall x. mem x r <==> x = a \/ mem x l);
       assert (x < a);
       //admitP(forall y. mem y xs ==> x <= y); (* Showing [admitP] *)
       assert (sorted r);
       r
*)

val sorted_smaller_:
  x:int ->
  xs:list int ->
  m:int ->
  Lemma (requires (sorted (x::xs) /\ mem m xs))
        (ensures (x <= m))
let rec sorted_smaller_ x xs m =
  match xs with
  | [] -> ()
    // sorted (x::[]) /\ mem m [] |= x <= m
    // sorted (x::[]) /\ False |= x <= m
  | y::ys ->
    if y=m
    then ()
      // y = m /\ sorted (x::y::ys) /\ mem m (y::ys) |= x <= m
      // subst: sorted (x::m::ys) |= x <= m
      // simplify: x <= m /\ sorted (m::ys) |= x <= m
    else
      // y != m /\ sorted (x::y::ys) /\ mem m (y::ys) |= x <= m
      // invert: sorted (x::y::ys) /\ mem m ys |= x <= m
      // simplify: x <= y /\ sorted (y::ys) /\ mem m ys |= x <= m
      sorted_smaller_ x ys m
      // preconditions: (1) sorted (x::ys) <== x <= y /\ sorted (y::ys) (by assumption)
      //                (2) mem m ys (by assumption)
      // postcondition: x <= m (QED)

val sorted_smaller:
  x:int ->
  xs:list int ->
  Lemma (requires (sorted (x::xs)))
        (ensures (forall y. mem y xs ==> x <= y))
        (decreases (length (x::xs))) // interesting termination measure
let rec sorted_smaller x xs =
  match xs with
  | [] -> ()
  | y::ys ->
      sorted_smaller_ x xs y; //Proves x <= y
      sorted_smaller y ys //Proves the rest of the list

val insert_sorted__ :
  a:int ->
  l:list int{sorted l} ->
  Tot (r:list int{sorted r /\ (forall x. mem x r <==> x=a \/ mem x l)})
let rec insert_sorted__ a l = match l with
  | [] -> [a]
  | x::xs ->
     if a <= x then
       a::l
     else begin
       sorted_smaller x xs;
       x::insert_sorted__ a xs
     end

(* Use of SMTpat *)

val sorted_smaller_smtpat:
  x:int ->
  xs:list int ->
  m:int ->
  Lemma (requires (sorted (x::xs) /\ mem m xs))
        (ensures (x <= m))
        [SMTPat (sorted (x::xs)); SMTPat (mem m xs)]
let rec sorted_smaller_smtpat x xs m = match xs with
    | [] -> ()
    | y::ys -> if y=m then () else sorted_smaller_smtpat x ys m

val insert_sorted :
  a:int ->
  l:list int{sorted l} ->
  Tot (r:list int{sorted r /\ (forall x. mem x r <==> x==a \/ mem x l)})
let rec insert_sorted a l = match l with
  | [] -> [a]
  | x::xs ->
     if a <= x then
       a::l
     else
       x::insert_sorted a xs

(* Insertion sort *)
val sort :
  l:list int ->
  Tot (m:list int{sorted m /\ (forall x. mem x l == mem x m)})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert_sorted x (sort xs)

(*****************************************************************************)

(** Swivel *)

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val rightmost : tr:tree -> Tot (option int)
let rec rightmost tr =
  match tr with
  | Leaf -> None
  | Node v _ rt ->
    match rt with
    | Leaf -> Some v
    | _ -> rightmost rt

val leftmost : tr:tree -> Tot (option int)
let rec leftmost tr =
  match tr with
  | Leaf -> None
  | Node v lt _ ->
    match lt with
    | Leaf -> Some v
    | _ -> leftmost lt

(*
val swivel : tr:tree -> r:tree{rightmost tr = leftmost r}
let rec swivel tr =
  match tr with
  | Leaf -> Leaf
  | Node v lt rt ->
      Node v (swivel rt) (swivel lt)
*)

val root : tr:tree -> Tot (option int)
let root tr = match tr with
  | Leaf -> None
  | Node v _ _ -> Some v

(*
val swivel : tr:tree -> r:tree{rightmost tr = leftmost r}
let rec swivel tr =
  match tr with
  | Leaf -> Leaf
  | Node v lt rt ->
      let ih1 = rightmost lt = leftmost (swivel lt) in
      let ih2 = rightmost rt = leftmost (swivel rt) in
      assert (ih1);
      assert (ih2);
      //admitP (root rt = root (swivel rt));
      let r = Node v (swivel rt) (swivel lt) in
      assert (ih1 /\ ih2 ==>  rightmost tr = leftmost r);
      r
*)

val swivel2 :
  tr:tree ->
  r:tree{rightmost tr = leftmost r /\ root tr = root r}
let rec swivel2 tr =
  match tr with
  | Leaf -> Leaf
  | Node v lt rt ->
      (* let ih1 = rightmost lt = leftmost (swivel2 lt) in
      let ih2 = rightmost rt = leftmost (swivel2 rt) in
      assert (ih1);
      assert (ih2);
      assert (rightmost tr = leftmost (Node v (swivel2 rt) (swivel2 lt))); *)
      Node v (swivel2 rt) (swivel2 lt)