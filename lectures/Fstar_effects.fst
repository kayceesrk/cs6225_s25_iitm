module Fstar_effects

open FStar.All
open FStar.Ref
open FStar.Mul


(*******************************************************************************)

(* F* is an effectful language *)
val incr : r:ref int -> St unit
let incr r = (r := (!r + 1))

(* Hoare Logic style pre- and post-conditions:

 [St a = ST a (requires (fun h_pre -> True)) (ensures (fun h_pre v h_post -> True)))]

  h_pre  := Initial heap
  h_post := Final heap
  v      := Result of the computation
*)

val incr2 : r:ref int -> ST unit (requires (fun h0 -> True))
  (ensures (fun h0 _ h2 -> modifies !{r} h0 h2 /\ sel h2 r == sel h0 r + 1))
let incr2 r = r := !r + 1

(** Heap and ST interfaces (much simplified)

module Heap (* Used for specification *)
  val heap : Type
  val ref : Type -> Type

  (* [Gtot] is ghost total effect. Ghost ~= computationally irrelevant *)
  val sel : #a:Type -> heap -> ref a -> GTot a
  (* Abstract heap is modelled as a map from [nat] to arbitrary typed values *)
  val addr_of: #a:Type -> ref a -> GTot nat

  let modifies (s:set nat) (h0 h1 : heap) : Type0 =
  (forall (a:Type) (r:ref a).
    (~(addr_of r `mem` s)) ==> sel h1 r == sel h0 r)


module ST (* Used for programming *)
  val (!): #a:Type -> r:ref a -> ST a
    (requires (fun (h0:heap) -> True))
    (ensures (fun h0 (x:a) h1 -> modifies !{} h0 h1 /\ x == sel h0 r))

  val (:=): #a:Type -> r:ref a -> v:a -> ST unit
    (requires (fun (h0:heap) -> True))
    (ensures (fun h0 _ h1 -> modifies !{r} h0 h1 /\ sel h1 r == v))

*)

(* verifying [incr] intuition *)

val incr3 : r:ref int -> ST unit (requires (fun h0 -> True))
  (ensures (fun h0 _ h2 -> exists h1 x. modifies !{ } h0 h1 /\ x == sel h0 r /\
                                        modifies !{r} h1 h2 /\ sel h2 r == x+1))
let incr3 r = let x = !r in r := x + 1

(* The post-condition can be simplified to *)

val incr4 : r:ref int -> ST unit (requires (fun h0 -> True))
    (ensures (fun h0 _ h2 -> modifies !{r} h0 h2 /\ sel h2 r == sel h0 r + 1))
let incr4 r = let x = !r in r := x + 1

(* thanks to the transitivity of modifies function *)

let modifies_trans (#a:Type) (s01 s12 : set nat) (h0 h1 h2 : heap) :
  Lemma (requires (modifies s01 h0 h1 /\ modifies s12 h1 h2))
        (ensures (modifies (s01 `Set.union` s12) h0 h2)) = ()


(* How does F* actually verfify [incr3]?
    + F* has support for pre-condition and post-condition inference.
    + Inference is syntax-directed and is similar to the rules that we had seen
      for Hoare logic

   Here is the rule for [let x1 = e1 in e2]:

    G |- e1 : ST t1 (requires (fun h0 -> pre))
                    (ensures (fun h0 x1 h1 -> post))
    G, x1:t1 |- e2 : ST t2 (requires (fun h1 -> exists h0. post))
                           (ensures (fun h1 x2 h2 -> post'))
    ---------------------------------------------------------------------------
    G |- let x1 = e1 in e2 : ST t2 (requires (fun h0 -> pre))
                                   (ensures (fun h0 x2 h2 -> exists x1 h1. post /\ post'))

 *)

val incr5 : r:ref int -> ST unit (requires (fun h0 -> True))
    (ensures (fun h0 _ h2 -> modifies !{r} h0 h2 /\ sel h2 r == sel h0 r + 1))
let incr5 r =
  let x = !r in
  (* Know (P1): exists h1 x. modified !{} h0 h1 /\ x == sel h0 r *)
  r := x + 1
  (* Know (P2): modifies !{r} h1 h2 /\ sel h2 r == x + 1*)

  (* [modifies !{r} h0 h2] directly follows from transitivity of modifies

     [sel h2 r == sel h0 r + 1] directly follows from (P1) and (P2) *)

(*******************************************************************************)

val swap0 : ref int -> ref int -> St unit
let swap0 r1 r2 =
  let t = !r1 in
  r1 := !r2;
  r2 := t

val swap : r1:ref int -> r2:ref int -> ST unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h3 -> modifies !{r1,r2} h0 h3 /\
                             sel h3 r2 == sel h0 r1 /\ sel h3 r1 == sel h0 r2))
let swap r1 r2 =
  let t = !r1 in
    (* Know (P1): exists h1 t. modifies !{} h0 h1 /\ t == sel h0 r1 *)
  r1 := !r2;
    (* Know (P2): exists h2. modifies !{r1} h1 h2 /\ sel h2 r1 == sel h1 r2 *)
  r2 := t
    (* Know (P3): modifies !{r2} h2 h3 /\ sel h3 r2 == t *)

    (* `modifies !{r1,r2} h0 h3` follows directly from transitivity of modifies *)

    (* `sel h3 r2 == sel h0 r1` follows immediately from (P1) and (P3) *)

    (* Still to show: `sel h3 r1 == sel h0 r2`
      From (P2) we know that  `sel h2 r1 == sel h1 r2` (A)
      From (P1) we know that  modifies !{} h0 h1
        which by definition gives us  sel h1 r2 == sel h0 r2 (B)
      From (P3) we know that  modifies !{r2} h2 h3
        which by definition gives us  sel h2 r1 == sel h3 r1 (C)
      We conclude by transitivity from (A)+(B)+(C) *)

(* This variant is correct even when r1 and r2 are aliased *)

(* Here is a funny way to do swap *)

val swap_add_sub : r1:ref int -> r2:ref int -> ST unit
    (requires (fun h0 -> addr_of r1 <> addr_of r2 ))
    (ensures (fun h0 _ h1 -> modifies !{r1,r2} h0 h1 /\
                            sel h1 r1 == sel h0 r2 /\ sel h1 r2 == sel h0 r1))
let swap_add_sub r1 r2 =
  r1 := !r1 + !r2;
  r2 := !r1 - !r2;
  r1 := !r1 - !r2

(* Correctness of this variant relies on
     1. r1 and r2 not being aliased
     2. int being unbounded (mathematical) integers

Exercise: sketch hand proof that this code is correct
*)

(*******************************************************************************)

(* Stateful count: 1 + 1 + 1 + ... *)

let rec count_st' (r:ref nat) (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> sel h1 r == sel h0 r + n /\ modifies !{r} h0 h1)) =
  if n > 0 then (r := !r + 1; count_st' r (n-1))

let rec count_st (n:nat) : ST nat (requires (fun h0 -> True))
    (ensures (fun h0 x h1 -> x == n /\ modifies !{} h0 h1)) =
  let r = alloc 0 in count_st' r n; !r

(* The truth about modifies and allocation (kind of, still simplified)


  module Heap (* Used for specification *)

    val contains : #a:Type -> heap -> ref a -> Type0

    let modifies (s:FStar.TSet.set nat) (h0 h1 : heap) : Type0 =
      (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
        (~(addr_of r `FStar.TSet.mem` s) /\ h0 `contains` r) ==> sel h1 r == sel h0 r)

    val alloc : #a:Type -> init:a -> ST (ref a)
      (requires (fun (h0:heap) -> True))
      (ensures (fun h0 r h1 -> modifies !{} h0 h1 /\ sel h1 r == init /\
                              ~(h0 `contains` r) /\ h1 `contains` r))
*)

(* Stateful count: 1 + 2 + 3 + ... *)

let sum_tot (n:nat) = ((n+1) * n) / 2

let rec sum_st' (r:ref nat) (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> modifies !{r} h0 h1 /\ sel h1 r == sel h0 r + sum_tot n)) =
  if n > 0 then (r := !r + n; sum_st' r (n-1))

let rec sum_st (n:nat) : ST nat (requires (fun h0 -> True))
    (ensures (fun h0 x h1 -> x == sum_tot n /\ modifies !{} h0 h1)) =
  let r = alloc 0 in sum_st' r n; !r

(* Stateful Fibonacci: 1 + 1 + 2 + 3 + 5 + 8 + … *)

let rec fibonacci (n:nat) : Tot nat =
  if n <= 1 then 1 else fibonacci (n-1) + fibonacci (n-2)

let rec fibonacci_st' (i:pos) (n:nat{n >= i}) (r1 r2:ref nat) : ST unit
          (requires (fun h0 -> addr_of r1 <> addr_of r2 /\
                            sel h0 r1 = fibonacci (i-1) /\
                            sel h0 r2 = fibonacci i))
          (ensures (fun h0 a h1 -> sel h1 r1 = fibonacci (n-1) /\
                                sel h1 r2 = fibonacci n /\
                                modifies !{r1,r2} h0 h1)) =
  if i < n then
    (let temp = !r2 in
     r2 := !r1 + !r2;    (* fibonacci (i+1) = fibonacci i + fibonacci (i-1) *)
     r1 := temp;                             (* fibonacci i we already have *)
     fibonacci_st' (i+1) n r1 r2 (* tail-recursive call to compute the rest *))

let fibonacci_st (n:nat) : ST nat (requires (fun h0 -> True))
      (ensures (fun h0 x h1 -> x = fibonacci n /\ modifies !{} h0 h1)) =
  if n <= 1 then 1
  else (let r1 = alloc 1 in
        let r2 = alloc 1 in
        fibonacci_st' 1 n r1 r2;
        !r2)
