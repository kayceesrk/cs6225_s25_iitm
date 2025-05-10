module Midterm

open FStar.List.Tot

(* In this module, we will describe and prove properties about vector clocks.
   For more information about vector clocks, see:
   https://en.wikipedia.org/wiki/Vector_clock.

	 You solution should not contain any [admit()] or equivalent. *)

(* The type of vector clock indexed by length *)
type t (n:nat) = lst:list nat{n > 0 && length lst = n}

type ordering =
| Happened_before
| Happened_after
| Concurrent
| Equal

val compare : v1:list nat -> v2:list nat{length v1 = length v2} -> ordering
let rec compare v1 v2 =
  match v1, v2 with
  | [], [] -> Equal
  | x::xs, y::ys ->
      if x = y then compare xs ys
      else if x < y then
        match compare xs ys with
        | Equal | Happened_before -> Happened_before
        | _ -> Concurrent
      else match compare xs ys with
           | Equal | Happened_after -> Happened_after
           | _ -> Concurrent

val hb: n:nat -> v1:t n -> v2:t n -> bool
let hb n a b = compare a b = Happened_before

val hbeq: n:nat -> v1:t n -> v2:t n -> bool
let hbeq n a b =
  match compare a b with
  | Happened_before | Equal -> true
  | _ -> false

(* 5 points *)
val hbeq_reflexive : n:nat -> v:t n -> Lemma (ensures (hbeq n v v))
let hbeq_reflexive n v = admit ()

(* 10 points *)
val hbeq_transitive : n:nat -> v1:t n -> v2:t n{hbeq n v1 v2} -> v3:t n{hbeq n v2 v3}
                    -> Lemma (ensures (hbeq n v1 v3))
let hbeq_transitive n v1 v2 v3 = admit ()

val concurrent : n:nat -> v1:t n -> v2:t n -> bool
let concurrent n v1 v2 = compare v1 v2 = Concurrent

(* 15 points *)
val concurrent_commutative : n:nat -> v1:t n -> v2:t n{concurrent n v1 v2}
                           -> Lemma (ensures (concurrent n v2 v1))
let concurrent_commutative n v1 v2 = admit ()
