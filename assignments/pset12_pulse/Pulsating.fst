module Pulsating
#lang-pulse
open Pulse
open Pulse.Lib.Pervasives

(******************************************************************************)
(* Swap3 (5 points) *)
(******************************************************************************)
(* The following shows a pulse [swap] function that swaps the values of two
   references. Implement a [swap3] function that swaps the values of three
   references [r1], [r2], and [r3]. The function should swap the values in such
   a way that [r1] gets the value of [r3], [r2] gets the value of [r1], and [r3]
   gets the value of [r2]. *)

fn swap #a (r1:ref a) (r2:ref a)
requires pts_to r1 'v1 ** pts_to r2 'v2
ensures pts_to r1 'v2 ** pts_to r2 'v1
{
  let v1 = !r1;
  let v2 = !r2;
  r2 := v1;
  r1 := v2
}

(******************************************************************************)
(* Mutable Tribonacci (10 points) *)
(******************************************************************************)

(* We have seen the mutable implementation of Fibonacci in the FStar effects
   lecture where we proved that it satisfies the functional specification.
   Similarly, we have seen Fibonacci implementation in Pulse. Implement a Pulse
   version of Tribonacci numbers, and prove it correct according to the spec
   below: *)

let rec tribonacci (n:nat) : nat =
  if n = 0 then 0
  else if n = 1 then 0
  else if n = 2 then 1
  else tribonacci (n - 1) + tribonacci (n - 2) + tribonacci (n - 3)

(* You will need to use 3 mutable references *)
fn trib_mut (n:nat)
requires emp
returns r:nat
ensures pure (tribonacci n = r)
{
  admit ();
}

(******************************************************************************)
(* Array.find (20 points) *)
(******************************************************************************)

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open FStar.SizeT
open Pulse.Lib.BoundedIntegers


(* You can see the implementation of a [Array.fill] function below for
   reference. *)

fn fill (#t:Type0) (l:SZ.t) (a:larray t (SZ.v l)) (v:t)
  requires pts_to a 's
  ensures exists* (s:Seq.seq t).
    pts_to a s **
    pure (s `Seq.equal` Seq.create (SZ.v l) v)
{
  pts_to_len a #1.0R #'s;
  let mut i = 0sz;
  while (let vi = !i; (vi < l))
  invariant b. exists* (vi:SZ.t) (s:Seq.seq t). (
    pts_to i vi **
    pts_to a s **
    pure (vi <= l
        /\ Seq.length s == SZ.v l
        /\ (b == (vi < l))
        /\ (forall (i:nat). i < SZ.v vi ==> Seq.index s i == v)))
  {
    let vi = !i;
    (a.(vi) <- v);
    i := vi + 1sz;
  }
}

(* Your job is to implement an [Array.find] function that satisfies the
   following signature. *)

fn find (#t:Type0) (l:SZ.t) (p:t->bool) (a:array t) (#s:erased (Seq.seq t))
requires
  pts_to a s **
  pure (Seq.length s == SZ.v l)
returns r:bool
ensures
  (pts_to a s **
  pure (Seq.length s == SZ.v l
        /\ (r <==> exists (i:nat). i < SZ.v l /\ p (Seq.index s i))))
{
  admit ();
}


(******************************************************************************)
(* List reverse (20 points) *)
(******************************************************************************)

(* Write a function in Pulse that reverses a linked list in place, and show
   that it is correct.

   Note: It is ok for the solution to not be O(n). O(n) solution may make use
   of functions that we have seen in the lectures. *)
