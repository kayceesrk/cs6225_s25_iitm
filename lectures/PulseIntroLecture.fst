module PulseIntroLecture
#lang-pulse
open Pulse

(* Please refer to https://fstar-lang.org/tutorial/book/pulse/pulse.html for the
   source materials where this lecuture is based on. *)

(******************************************************************************)
(* Section: Pulse Basics *)
(******************************************************************************)

(*

Separation Logic Primer
-----------------------

{ P } c { \v. Q }

where `P` and `Q` are separation logic predicates `slprop`s. `slprop` stands for
separation logic predicates.

type slprop = state -> prop

where `state` is the state of the heap.

*)

let fstar_five : int = 5

fn five ()
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  fstar_five
}

let pulse_five_in_fstar = five ()
let pulse_five : int = 5

(*

The above is a convenient way to write

```
{ emp } five () { n:int. pure (n == 5) }.
```

*)

(*

Some simple slprops:
--------------------
* `emp`, the trivial proposition (equivalent to `fun s -> True`).
* `pure p`, heap-independent predicate `fun s -> p` where s ∉ fv(p).
   + `emp` is equivalent to `pure True`.

Ownership and permission
------------------------
* Key idea is the concept of ownership.
  + A computation can only access those resources that it is explicitly granted
    access to in its precondition or those that it creates itself.
  + `five` cannot access any resources, because its precondition is `emp`.
    - This is different from ST effect in F*. See `incr` in
      `PureIntroSupport.fst`.
*)

[@@expect_failure]
fn five' (x : ref int)
  requires emp
  returns n:int
  ensures pure (n == 5)
{
  let v = !x;
  x := v + 1;
  fstar_five
}

fn incr (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}

fn incr_explicit_i (x:ref int) (i:erased int)
  //[erased] turns a type into a ghost type i.e, computationally irrelevant.
requires pts_to x i (* explicitly bound logical variable *)
ensures pts_to x (i + 1)
{
    let v = !x;
    x := v + 1;
}

(* STOPPED HERE 04/04/25 *)

(*

Separation Logic Rules
----------------------

## Connectives in Separation Logic

Connectives of separation logic in terms of the sets of partial
heaps that they accept.

(1) emp = {●}
(2) pts_to x v = {●[x -> v]}
(3) pure P = {h | P /\ h = ●}
(3) exists* x. P = {h | exists x. h ∈ P(x)}
(4) P ** Q = {h1 ⨄ h2 | h1 ∈ P /\ h2 ∈ Q}
      ^^ is "separating conjunction"
(5) p @==> q = {h | h ∈ p ==> h ∈ q}
      ^^ is "separating implication"

## Properties

* Commutative : P ** Q @==> Q ** P
* Associative : P ** (Q ** R) @==> (P ** Q) ** R
* Idempotent  : P ** emp @==> P
* Frame rule  :

       {P} c {Q}
  -------------------
  {P ** R} c {Q ** R}

  + Captures the essence of local modular reasoning
  + If a program is correct with permission `P` then it is correct in a larger
    context with additional permissions `R` which it doesn't touch.

*)

(* Thanks to the frame rule, the following need not mention anything about `y`.
   This is not true with ST effect in F*. See `incr3` in
   `PulseIntroSupport.fst` *)

fn incr_frame (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
   incr x;
   incr y;
}

(* In fact, Pulse lets us use the frame rule with any `f:slprop`, and we get,
   for free, that `incr x` does not disturb `f`. *)

fn incr_frame_any (x:ref int) (f:slprop)
requires pts_to x 'i ** f
ensures pts_to x ('i + 1) ** f
{
   incr x;
}

(******************************************************************************)
(* Section: Mutable References *)
(******************************************************************************)

(*

* Aim to have memory management without GC
  + Be able to target C or Rust
* Different kinds of references
  + Stack, Heap and Ghost

*)

(* [ref t] type is agnostic to whether it is in heap or stack. Comes from
   [Pulse.Lib.Reference.ref t]. We write programs over [ref t] and then use it
   with both Stack and Heap references. *)

fn swap #a (r0 r1:ref a)
requires pts_to r0 'v0 ** pts_to r1 'v1
ensures pts_to r0 'v1 ** pts_to r1 'v0
{
    let v0 = !r0;
    let v1 = !r1;
    r0 := v1;
    r1 := v0;
}

(* Reading a reference *)

fn value_of (#a:Type) (r:ref a)
requires pts_to r 'v
returns v:a
ensures pts_to r 'v ** pure (v == 'v)
{
    !r;
}

fn value_of_explicit (#a:Type) (r:ref a) (#w:erased a)
requires pts_to r w
returns v:a
ensures pts_to r w ** pure (v == reveal w)
{
    !r;
}

[@@expect_failure]
fn value_of_explicit_fail (#a:Type) (r:ref a) (#w:erased a)
requires pts_to r w
returns v:a
ensures pts_to r w ** pure (v == reveal w)
{
    reveal w (* cannot use erased values in non-ghost computations *)
}

(* Writing to a reference *)

fn assign (#a:Type) (r:ref a) (v:a)
requires pts_to r 'v
ensures pts_to r v
{
    r := v;
}

fn add (r:ref int) (n:int)
requires pts_to r 'v
ensures pts_to r ('v + n)
{
    let v = !r;
    r := v + n;
}

open FStar.Mul

fn quadruple (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r;
    add r v1;
    let v2 = !r;
    add r v2;
}

(* Pulse type checking has two components)
   1. Typing environment
   2. `slprop` context (or context for short)

   If {p ** q} goal {r ** q} holds and {p} goal {r} also holds, then we call [p]
   the "support" of [goal] and [q] the "frame" of [goal].
*)

[@@expect_failure] //comment this line to see the output of [show_proof_state]
fn quadruple' (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    let v1 = !r; // Env=v1:int; _:squash (v1 == 'v)       Ctxt= pts_to r v1
    add r v1;    // ...                                   Ctxt= pts_to r (v1 + v1)
    let v2 = !r; // Env=...; v2:int; _:squash(v2==v1+v1)  Ctxt= pts_to r v2
    add r v2;    // Env=...                               Ctxt= pts_to r (v2 + v2)
                 // ..                                    Ctxt= pts_to r (4 * 'v)
    show_proof_state;

}

[@@expect_failure] //Stateful commands are explicitly sequenced
fn quad_fail (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
    add r (!r);
    add r (!r);
}

(* STOPPED HERE: 07/04/25 *)

(* Fractional Permissions *)

(* Actual type of [pts_to]) is:

   val pts_to (#a:Type u#0) (r:ref a) (#p:perm) (v:a) : vprop

  The [perm] argument is interesting.
  * 1.0R default
  * 0.0R < p <= 1.0R
  * Write requires 1.0R
  * Read can be done at any value of perm.
*)

fn assign_full_perm (#a:Type) (r:ref a) (v:a)
requires pts_to r #1.0R 'v
ensures pts_to r #1.0R v
{
    r := v;
}

fn value_of_perm #a #p (r:ref a)
requires pts_to r #p 'v
returns v:a
ensures pts_to r #p 'v ** pure (v == 'v)
{
    !r;
}

#push-options "--print_implicits"
[@@expect_failure]
fn assign_perm #a #p (r:ref a) (v:a) (#w:erased a)
requires pts_to r #p w
ensures pts_to r #p w
{
    r := v;
}
#pop-options

fn share_ref #a #p (r:ref a)
requires pts_to r #p 'v
ensures pts_to r #(p /. 2.0R) 'v ** pts_to r #(p /. 2.0R) 'v
{
    share r;
}

fn gather_ref #a (#p:perm) (r:ref a)
requires
    pts_to r #(p /. 2.0R) 'v0 **
    pts_to r #(p /. 2.0R) 'v1
ensures
    pts_to r #p 'v0 **
    pure ('v0 == 'v1) //pointed-to witnesses are equal
{
    gather r
}

(* [let mut] creates a new stack ref *)
fn one ()
requires emp
returns v:int
ensures pure (v == 1)
{
                   //     .     |- emp
    let mut i = 0; // i:ref int |- pts_to i 0
    incr i;        // i:ref int |- pts_to i (0 + 1)
    !i             //      .    |- v:int. emp ** pure (v == 1)
}

[@@expect_failure]
fn refs_are_scoped ()
requires emp
returns s:ref int
ensures pts_to s 0
{
    let mut s = 0;
    s
}

module Box = Pulse.Lib.Box
(* For heap references. Like Rust's Box<T>. Box has the functions pts_to, (!),
   (:=), share, gather, alloc and free. *)

fn new_heap_ref (#a:Type) (v:a)
requires emp
returns r:Box.box a
ensures Box.pts_to r v
{
    Box.alloc v
}

fn last_value_of #a (r:Box.box a)
requires Box.pts_to r 'v
returns v:a
ensures pure (v == 'v)
{
    open Box;
    let v = !r;
    free r;
    v
}

(* [box t] references can be demoted to regular [ref t] references for code
   reuse. *)
fn incr_box (r:Box.box int)
requires Box.pts_to r 'v
ensures Box.pts_to r ('v + 1)
{
    Box.to_ref_pts_to r;     //pts_to (box_to_ref r) 'v
    incr (Box.box_to_ref r); //pts_to (box_to_ref r) ('v + 1)
    Box.to_box_pts_to r      //Box.pts_to r ('v + 1)
}

(******************************************************************************)
(* Section: Existential quantification *)
(******************************************************************************)

(* Examples: [exists*] is an [slprop -> slprop] constructor.

- exists* (v:nat). pts_to x v
- exists* v. pts_to x v
- exists* v1 v2. pts_to x v1 ** pts_to y v2

*)

fn assign2 (#a:Type) (r:ref a) (v:a)
requires pts_to r 'v
ensures pts_to r v
{
    r := v;
}

fn assign2' #a (x:ref a) (v:a)
requires
  exists* w. pts_to x w
ensures
  pts_to x v
{
  x := v
}

[@@expect_failure]
fn incr #a (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  pts_to x (w0 + 1) //w0 is not in scope here
{
  let w = !x
  x := w + 1
}

(* Existential quantification often appears in postconditions, e.g., in order to
   abstract the behavior of function by underspecifying it. *)

fn make_even (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  let v = !x;
  x := v + v;
}

(* Manipulating existentials

   F* automatically manipulates existentials. But sometimes it is useful to know
   how to manage them explicitly.

  [with w0...wn. assert p; rest] eliminates existentials when the context
   contains [exists* x0...xn. p].

   [with] construct binds [w0...wn] to the existentially quantified variables
   [x0...xn] in the remainder of the scope [rest]. *)


fn make_even_explicit (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  //show_proof_state;
  with w0. assert (pts_to x w0);
  let v = !x; // v:int; _:squash(v==w0); Ctxt=pts_to x v
  x := v + v; //                          ... pts_to x (v + v)
  //show_proof_state;
  introduce
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
  with (v + v);
  //show_proof_state;
}

(* [introduce exists* x1..xn. p with w1..wn] introduces existentials [x1..xn] in
   the context with witnesses [w1..wn] *)

(* When there is a single existential formula in the context, one can write with
   [x1..xn. _] to "open" the formula, binding its witnesses in scope. *)
fn make_even_explicit_alt (x y:ref int)
requires
  exists* wx wy. pts_to x wx ** pts_to y wy ** pure (wx % 2 == wy % 2)
ensures
  exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
{
  //show_proof_state;
  with wx wy. _;
  //show_proof_state;
  let vx = !x;
  let vy = !y;
  x := vx + vy;
  introduce exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
  with (vx + vy) vy;
}


(******************************************************************************)
(* Section: User-defined Predicates *)
(******************************************************************************)

let pts_to_diag
        #a
        (r:ref (a & a))
        (v:a)
: slprop
= pts_to r (v, v) //points to a pair with the same values

fn double (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold (pts_to_diag r 'v); //What is [unfold]?
  //show_proof_state;
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  //show_proof_state;
  fold (pts_to_diag r v2); //What is [fold]?
}

fn double_alt (r:ref (int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold pts_to_diag; //NOTE: arugments not provided
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold pts_to_diag; //NOTE: arugments not provided
}

(* Mutable points *)

noeq
type point = {
    x:ref int;
    y:ref int;
}

//[is_point] is a "representation predicate" for [point] type.
let is_point (p:point) (xy: int & int) =
    pts_to p.x (fst xy) **
    pts_to p.y (snd xy)

fn move (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point; //NOTE: arguments are not provided
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  //show_proof_state;
  fold (is_point p (x + dx, y + dy));
    //Pulse cannot infer the instantiation of [is_point] when folding it.
}

(* STOPPED HERE 09/04 *)

(* Package into convenient helper function *)
ghost
fn fold_is_point (p:point)
requires pts_to p.x 'x ** pts_to p.y 'y
ensures is_point p (reveal 'x, reveal 'y)
{
  fold (is_point p (reveal 'x, reveal 'y))
}

fn move_alt (p:point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold_is_point p;
}

(* Rewriting

    with x1 ... xn. rewrite p as q;
    rest

*)

fn create_and_move ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    //pts_to x 0 ** pts_to y 0
    with _v. rewrite pts_to x _v as pts_to p.x _v;
    with _v. rewrite pts_to y _v as pts_to p.y _v;
    //pts_to p.x 0 ** pts_to p.y 0
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    //pts_to p.x (fst (1, 1)) ** pts_to p.y (snd (1, 1))
    with _v. rewrite pts_to p.x _v as pts_to x _v;
    with _v. rewrite pts_to p.y _v as pts_to y _v;
    //pts_to x (fst (1, 1)) ** pts_to y (snd (1, 1))
}

fn create_and_move_alt ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    rewrite each
      x as p.x, y as p.y;
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    rewrite each
      p.x as x, p.y as y;
}


(******************************************************************************)
(* Section: Conditional *)
(******************************************************************************)

let max_spec x y = if x < y then y else x

fn max #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    {
        vx
    }
    else
    {
        vy
    }
}

[@@expect_failure]
fn max_alt #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let mut result = 0;
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    {
        result := vx;
    }
    else
    {
        result := vy;
    };
    !result;
}

fn max_alt #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let mut result = 0;
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    ensures
     exists* r.
       pts_to x #p 'vx **
       pts_to y #q 'vy **
       pts_to result r **
       pure (r == max_spec 'vx 'vy)
    {
        result := vx;
    }
    else
    {
        result := vy;
    };
    !result;
}

(* Pattern matching with nullable references *)

let nullable_ref a = option (ref a)

(* Representation Predicate *)
let pts_to_or_null #a
        (x:nullable_ref a)
        (#[default_arg (`1.0R)] p:perm) //implicit argument with a default
        (v:option a)
: slprop
= match x with
  | None -> pure (v == None)
  | Some x -> exists* w. pts_to x #p w ** pure (v == Some w)

fn read_nullable #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures pts_to_or_null r #p 'v
        ** pure ('v == o)
{
    match r {
     Some x -> {
        //show_proof_state;
        rewrite each r as (Some x);
        //show_proof_state;
        unfold (pts_to_or_null (Some x) #p 'v);
        let o = !x;
        fold (pts_to_or_null (Some x) #p 'v);
        //rewrite each (Some x) as r;
        Some o
     }
     None -> {
        rewrite each r as None;
        unfold (pts_to_or_null None #p 'v);
        fold (pts_to_or_null None #p 'v);
        rewrite each (None #(ref a)) as r;
        None #a
     }
    }
}

[@@expect_failure]
fn read_nullable_alt #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures emp
{
    match r {
     Some x -> { admit () }
     _ -> {
        // we only have `r == _` in scope
        // not the negation of the prior branch conditions
        // i.e., unlike F*, we don't have not (Some? r)
        // so the assertion below fails
        assert (pure (r == None)); //fails here without [@@expect_failre]
        admit() }
    }
}

(* Helper function for [pts_to_or_null] *)

ghost
fn elim_pts_to_or_null_none #a #p (r:nullable_ref a)
requires pts_to_or_null None #p 'v ** pure (r == None)
ensures pts_to_or_null r #p 'v ** pure ('v == None)
{
    rewrite each r as None;
    unfold (pts_to_or_null None #p 'v);
    fold (pts_to_or_null None #p 'v);
    rewrite each (None #(ref a)) as r;
}

ghost
fn intro_pts_to_or_null_none #a #p (r:nullable_ref a)
requires pure (r == None)
ensures pts_to_or_null r #p None
{
    fold (pts_to_or_null #a None #p None);
    rewrite each (None #(ref a)) as r;
}

ghost
fn elim_pts_to_or_null_some #a #p (r:nullable_ref a) (x:ref a)
requires pts_to_or_null (Some x) #p 'v
ensures exists* w. pts_to x #p w ** pure ('v == Some w)
{
    rewrite each r as (Some x);
    unfold (pts_to_or_null (Some x) #p 'v);
}

ghost
fn intro_pts_to_or_null_some #a #p (r:nullable_ref a) (x:ref a)
requires pts_to x #p 'v ** pure (r == Some x)
ensures pts_to_or_null r #p (Some 'v)
{
    fold (pts_to_or_null (Some x) #p (Some 'v));
    rewrite each (Some x) as r;
}

fn read_nullable_alt #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures pts_to_or_null r #p 'v
        ** pure ('v == o)
{
    match r {
     Some x -> {
        elim_pts_to_or_null_some r x;
        let o = !x;
        intro_pts_to_or_null_some r x;
        Some o
     }
     None -> {
        elim_pts_to_or_null_none r;
        None #a
     }
    }
}

fn write_nullable #a (r:nullable_ref a) (v:a)
requires pts_to_or_null r 'v
ensures exists* w. pts_to_or_null r w ** pure (Some? r ==> w == Some v)
{
    match r {
     None -> {
      //show_proof_state;
      rewrite each (None #(ref a)) as r;
      ()
     }
     Some x -> {
        elim_pts_to_or_null_some r x;
        x := v;
        intro_pts_to_or_null_some r x;
     }
    }
}

(******************************************************************************)
(* Section: Loops & Recursion*)
(******************************************************************************)

(*

while ( guard )
invariant (b:bool). p
{ body }

Where

* [guard] is a Pulse program that returns a b:bool
* [body] is a Pulse program that returns unit
* invariant (b:bool). p is an invariant where
  + [exists* b. p] must be provable before the loop is entered and as a
    postcondition of body.
  + [exists* b. p] is the precondition of the guard, and [p b] is its
    postcondition, i.e., the [guard] must satisfy:

      requires exists* b. p
      returns b:bool
      ensures p

One way to understand the invariant is that it describes program assertions at three different program points.

* When [b==true], the invariant describes the program state at the start of the
  loop body;
* when [b==false], the invariant describes the state at the end of the loop;
* when [b] is undetermined, the invariant describes the property of the program
  state just before the guard is (re)executed, i.e., at the entry to the loop
  and at the end of loop body.

*)

fn count_down (x:ref nat)
requires pts_to x 'v
ensures pts_to x (0 <: nat) //F* type inference infers this as [int]; force [nat]
{
    let mut keep_going = true;
    while (
        !keep_going
    )
    invariant b.
      exists* (v:nat).
        pts_to keep_going b **
        pts_to x v **
        pure (b == false ==> v == 0)
    {
        let n = !x;
        if (n = 0)
        {
            keep_going := false;
        }
        else
        {
            x := n - 1;
        }
    }
}

fn count_down2 (x:ref nat)
requires pts_to x 'v
ensures pts_to x (0 <: nat)
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        }
        else
        {
            x := n - 1;
            true
        }
    )
    invariant b.
      exists* (v:nat).
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}

fn count_down_loopy (x:ref nat)
requires pts_to x 'v
ensures pts_to x (0 <: nat)
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        }
        else
        {
            x := n + 1; //Loop never terminates
            true
        }
    )
    invariant b.
      exists* (v:nat).
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}

(* See the 1949 paper by Alan Turing titled "Checking a Large Routine" *)
fn multiply_by_repeated_addition (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr : nat = 0;
    let mut acc : nat = 0;
    while (
        let c = !ctr;
        (c < x)
    )
    invariant b.
    exists* (c:nat) (a:nat).
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              a == (c * y) /\
              b == (c < x))
    {
        let a = !acc;
        acc := a + y;
        let c = !ctr;
        ctr := c + 1;
    };
    !acc
}

let rec sum (n:nat)
: nat
= if n = 0 then 0 else n + sum (n - 1)

#push-options "--z3rlimit 20"
noextract //computationally irrelevant
let rec sum_lemma (n:nat)
: Lemma (sum n == n * (n + 1) / 2)
= if n = 0 then ()
  else
    sum_lemma (n - 1)
#pop-options

#push-options "--z3cliopt 'smt.arith.nl=false'"

fn isum (n:nat)
requires emp
returns z:nat
ensures pure ((n * (n + 1) / 2) == z)
{
    let mut acc : nat = 0;
    let mut ctr : nat = 0;
    while (
        let c = !ctr;
        (c < n)
    )
    invariant b.
    exists* (c:nat) (a:nat).
        pts_to ctr c **
        pts_to acc a **
        pure (c <= n /\
              a == sum c /\
              b == (c < n))
    {
        let a = !acc;
        let c = !ctr;
        ctr := c + 1;
        acc := a + c + 1;
    };
    //show_proof_state;
    sum_lemma n; //call an F* lemma inside Pulse
    //show_proof_state;
    !acc;
}

#pop-options

(* Recursive Pulse Programs *)

let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

//See [rec] keyword
fn rec fib_rec (n:pos) (out:ref (nat & nat))
requires
    pts_to out 'v
ensures
    exists* v.
        pts_to out v **
        pure (
          fst v == fib (n - 1) /\
          snd v == fib n
        )
{
  if ((n = 1))
  {
    //type inference in Pulse doesn't work well here:
    //it picks (1, 1) to have type (int & int)
    //so we have to annotate
    out := ((1 <: nat), (1 <: nat));
  }
  else
  {
    fib_rec (n - 1) out;
    let v = !out;
    out := (snd v, fst v + snd v);
  }
}

fn fib_loop (k:pos)
  requires emp
  returns r:nat
  ensures pure (r == fib k)
{
  let mut i : nat = 1;
  let mut j : nat = 1;
  let mut ctr : nat = 1;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b .
    exists* (vi:nat) (vj:nat) (vctr:nat).
        pts_to i vi **
        pts_to j vj **
        pts_to ctr vctr **
        pure (
            1 <= vctr /\
            vctr <= k /\
            vi == fib (vctr - 1) /\
            vj == fib vctr /\
            b == (vctr < k)
        )
  {
      let vi = !i;
      let vj = !j;
      let c = !ctr;
      ctr := c + 1;
      i := vj;
      j := vi + vj;
  };
  !j
}


(******************************************************************************)
(* Section: Mutable Arrays *)
(******************************************************************************)

(* [Pulse.Lib.Array.array t] is the basic array type.
   [Pulse.Lib.Vec.vec t] is heap-allocated arrays.

   We usually write functions on [Pulse.Lib.Array.array.t]  and use coercions to
   convert between [vec t] and [array t].
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array

module SZ = FStar.SizeT

 //readi$
fn read_i
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type)
  (arr:array t)
  (#p:perm)
  (#s:erased (Seq.seq t))
  (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr #p s
  returns x:t
  ensures pts_to arr #p s ** pure (x == Seq.index s (SZ.v i))
{
  arr.(i)
}

fn write_i
  (#t:Type)
  (arr:array t)
  (#s:erased (Seq.seq t))
  (x:t)
  (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr s
  ensures pts_to arr (Seq.upd s (SZ.v i) x)
{
  arr.(i) <- x
}

[@@ expect_failure]
fn write_ip (#t:Type) (arr:array t) (#p:perm) (#s:erased _) (x:t)
            (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr #p s
  ensures pts_to arr #p (Seq.upd s (SZ.v i) x)
{
  arr.(i) <- x
}

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
open FStar.SizeT

fn compare
  (#[@@@ Rust_generics_bounds ["PartialEq"; "Copy"]] t:eqtype)
  #p1 #p2
  (a1 a2:A.array t)
  (l:SZ.t)
  requires (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (res <==> Seq.equal 's1 's2)
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    if (vi <^ l) {
      let v1 = a1.(vi);
      let v2 = a2.(vi);
      (v1 = v2)
    } else {
      false
    }
  )
  invariant b.
  exists* vi. (
    R.pts_to i vi **
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l && Seq.index 's1 (SZ.v vi) = Seq.index 's2 (SZ.v vi))) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index 's1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    i := vi +^ 1sz
  };
  let vi = !i;
  let res = vi = l;
  res
}

(* [copy] contents of [a2] tp [a1] *)
fn copy
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type0)
  (a1 a2:A.array t)
  (l:SZ.t)
  (#p2:perm)
  requires (
    A.pts_to a1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  ensures (
    (exists* s1. A.pts_to a1 s1 ** pure (Seq.equal s1 's2)) **
    A.pts_to a2 #p2 's2
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    (vi <^ l)
  )
  invariant b.
  exists* vi s1. (
    R.pts_to i vi **
    A.pts_to a1 s1 **
    A.pts_to a2 #p2 's2 **
    pure (
      Seq.length s1 == Seq.length 's2 /\
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l)) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index s1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    let v = a2.(vi);
    a1.(vi) <- v;
    i := vi +^ 1sz
  }
}

fn copy2
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type0)
  (a1 a2:A.array t)
  (l:SZ.t)
  (#p2:perm)
  requires (
    A.pts_to a1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  ensures (
    A.pts_to a1 's2 **
    A.pts_to a2 #p2 's2 //Simpler post-condition
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    (vi <^ l)
  )
  invariant b.
  exists* vi s1. (
    R.pts_to i vi **
    A.pts_to a1 s1 **
    A.pts_to a2 #p2 's2 **
    pure (
      Seq.length s1 == Seq.length 's2 /\
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l)) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index s1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    let v = a2.(vi);
    a1.(vi) <- v;
    i := vi +^ 1sz
  };
  // after the loop
  with v1 s1. _; //bind existentially bound witnesses from the invariant
  Seq.lemma_eq_elim s1 's2; //call an F* lemma to prove that s1 == 's2
  ()
}

(* Stack allocated arrays *)

fn compare_stack_arrays ()
  requires emp
  ensures emp
{
  (* [| v; n |] allocates an array of size [n] with all elements set to [v] on
     the stack. The size [n] must be a compile time constant. *)

  // |- emp
  let mut a1 = [| 0; 2sz |];
  // a1:array int |- pts_to a1 (Seq.create 0 (SZ.v 2))
  let mut a2 = [| 0; 2sz |];
  // a1 a2:array int |- pts_to a1 (Seq.create 0 (SZ.v 2)) ** pts_to a2 (Seq.create 0 (SZ.v 2))
  let b = compare a1 a2 2sz;
  assert (pure b)
}

[@@ expect_failure]
fn ret_stack_array ()
  requires emp
  returns a:array int
  ensures pts_to a (Seq.create 2 0)
{
  let mut a1 = [| 0; 2sz |];
  a1  // cannot prove pts_to a (Seq.create 0 2) in the context emp
}

module V = Pulse.Lib.Vec

fn heap_arrays ()
  requires emp
  returns a:V.vec int
  ensures V.pts_to a (Seq.create 2 0)
{
  let a1 = V.alloc 0 2sz;
  let a2 = V.alloc 0 2sz;
  V.free a1;
  a2  // returning vec is ok
}

fn copy_app ([@@@ Rust_mut_binder] v:V.vec int)
  requires exists* s. V.pts_to v s ** pure (Seq.length s == 2)
  ensures V.pts_to v (Seq.create 2 0)
{
  let mut a = [| 0; 2sz |];
  // v, s |- V.pts_to v s ** ...
  //show_proof_state;
  V.to_array_pts_to v;
  //show_proof_state;
  // v, s |- pts_to (vec_to_array v) s ** ...
  copy2 (V.vec_to_array v) a 2sz;
  // v, s |- pts_to (vec_to_array v) (Seq.create 2 0) ** ...
  V.to_vec_pts_to v
  // v, s |- V.pts_to v (Seq.create 2 0) ** ...
}

(******************************************************************************)
(* Section: Implication and Universal Quantification *)
(******************************************************************************)

(*
   + Implication in Pulse is (@==>) to be read as "trade" operator.
   + Related to `--*` magic wand operator in the separation logic literature.

            p ** p @==> q                   r ** p |- q
           -------------- [Elim]            ----------------- [Intro]
                 q                            |- p @==> q
*)

module I = Pulse.Lib.Stick.Util
open Pulse.Lib.Stick
module GR = Pulse.Lib.GhostReference
open GR

ghost
fn __elim (p q:slprop)
requires p ** (p @==> q)
ensures q

ghost
fn __intro (p q r:slprop)
           (elim: unit -> stt_ghost unit emp_inames (r ** p) (fun _ -> q))
requires r
ensures p @==> q

let regain_half #a (x:GR.ref a) (v:a) =
  pts_to x #0.5R v @==> pts_to x v
(* You can gain full permissions if you have half permissions?! WAT!

   Trick is to know that [regain_half] holds the rest of the permission
   [exists* u. pts_to x #0.5R u] internally, packaged during introduction. *)

ghost
fn intro_regain_half (x:GR.ref int)
requires pts_to x 'v
ensures pts_to x #0.5R 'v ** regain_half x 'v
{
  ghost
  fn aux ()
  requires pts_to x #0.5R 'v ** pts_to x #0.5R 'v
  ensures pts_to x 'v
  {
    GR.gather x;
  };
  GR.share x;
  I.intro _ _ _ aux;
  //show_proof_state;
  fold regain_half;
}

ghost
fn use_regain_half (x:GR.ref int)
requires pts_to x #0.5R 'v ** regain_half x 'v
ensures pts_to x 'v
{
  unfold regain_half;
  I.elim _ _;
}

(* Want to clarify that in the simple usage (@==>) hasn't brought us much *)

(******************************************************************************)
(* Section: Linked Lists *)
(******************************************************************************)

open Pulse.Lib.Pervasives
open FStar.List.Tot

noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)

(* Representation predicate linking linked list to logic representation *)
let rec is_list #t (x:llist t) (l:list t)
: Tot slprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl ->
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl

(* Some boilerplate. TODO: Pulse will automate later. *)

ghost
fn elim_is_list_nil (#t:Type0) (x:llist t)
requires is_list x 'l ** pure ('l == [])
ensures pure (x == None)
{
   rewrite each 'l as Nil #t;
   unfold (is_list x [])
}

ghost
fn intro_is_list_nil (#t:Type0) (x:llist t)
requires pure (x == None)
ensures is_list x []
{
    fold (is_list x []);
}

ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (l:list t) (head:t) (tl:list t)
requires is_list x l ** pure (l == head::tl)
ensures (
  exists* (p:node_ptr t) (tail:llist t).
    pure (x == Some p) **
    pts_to p { head; tail } **
    is_list tail tl
)
{
  rewrite each l as (head::tl);
  unfold (is_list x (head::tl));
}

ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t)
                      (#node:node t) (#tl:list t)
requires
  pts_to v node **
  is_list node.tail tl **
  pure (x == Some v)
ensures
  is_list x (node.head::tl)
{
    rewrite (pts_to v node) as (pts_to v { head=node.head; tail=node.tail });
    fold (is_list x (node.head::tl));
}

(* Case analyzing a nullable pointer a.k.a more helper functions *)

let is_list_cases #t (x:llist t) (l:list t)
: slprop
= match x with
  | None -> pure (l == [])
  | Some v ->
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl

ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  match l {
    Nil -> {
      unfold (is_list x []);
      fold (is_list_cases None l);
      rewrite each (None #(ref (node t))) as x; //can be commented out?
    }
    Cons head tl -> {
      unfold (is_list x (head::tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
      fold (is_list_cases (Some v) l);
      //show_proof_state;
      rewrite each (Some #(ref (node t)) v) as x;
    }
  }
}

ghost
fn is_list_case_none (#t:Type) (x:llist t) (#l:list t)
requires is_list x l ** pure (x == None)
ensures is_list x l ** pure (l == [])
{
  cases_of_is_list x l;
  rewrite each x as (None #(ref (node t)));
  unfold (is_list_cases None l);
  fold (is_list x []);
}

ghost
fn is_list_case_some (#t:Type) (x:llist t) (v:node_ptr t) (#l:list t)
requires is_list x l ** pure (x == Some v)
ensures
  exists* (node:node t) (tl:list t).
    pts_to v node **
    is_list node.tail tl **
    pure (l == node.head::tl)
{
  cases_of_is_list x l;
  rewrite each x as (Some v);
  unfold (is_list_cases (Some v) l);
}

(* Length, recursively *)

fn rec length (#t:Type0) (x:llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  match x {
    None -> {
      //show_proof_state;
      // |- is_list None 'l
      is_list_case_none x;
      // |- is_list None 'l ** pure ('l == [])
      0
    }
    Some vl -> {
      // |- is_list (Some vl) 'l ** pure (x == Some vl)
      is_list_case_some x vl;
      // |- (exists* (node:node t) (tl:list t). pts_to vl node **
      //                                        is_list node.tail tl **
      //                                        pure ('l == node.head :: tl)) **
      //                                        pure (x == Some vl)
      with _node _tl. _;
      // |- pts_to vl _node ** is_list _node.tail _tl **
      //    pure ('l == _node.head :: _tl) ** pure (x == Some vl)
      let node = !vl;
      rewrite each _node as node;
      // |- pts_to vl node ** is_list node.tail tl ** pure ('l == node.head :: _tl)
      let n = length node.tail;
      //show_proof_state;
      // |- pts_to vl node ** is_list node.tail tl ** pure ('l == node.head :: _tl) ** pure (x == Some vl)
      //    pure (n == length node.tail) ** pure (n == List.Tot.length tl)
      intro_is_list_cons x vl;
      // |- is_list x (node.head :: _tl)
      (1 + n)
    }
  }
}

(* Length, Iteratively, with Trades *)

ghost
fn tail_for_cons (#t:Type) (v:node_ptr t) (#n:node t) (tl:erased (list t))
requires
  pts_to v n
ensures
  (is_list n.tail tl @==> is_list (Some v) (n.head::tl))
{
  ghost
  fn aux ()
  requires
    pts_to v n ** is_list n.tail tl
  ensures
    is_list (Some v) (n.head::tl)
  {
    intro_is_list_cons (Some v) v
  };
  I.intro _ _ _ aux;
}

(* Tail of a list

x             tl
|             |
v             v
.---.---.     .---.---.
|   | --|---> |   | --|--> ...
.---.---.     .---.---.

Basic operation: Given a pointer to [x], we ned to return [Some tl] pointer or
[None].

But, we have a permission accounting problem:

* We cannot return permission to [x] to the caller; will create aliases [tl] and
  [x->next].
* We cannot consume permission to [x]; we'd like to return permission to [x]
  when [tl] goes out of scope.

The solution is to a "trade".

*)

fn tail (#t:Type) (x:llist t)
requires is_list x 'l ** pure (Some? x) //x is a non-null pointer
returns y:llist t
ensures exists* tl.
    is_list y tl **
    (is_list y tl @==> is_list x 'l) **
      //you can recover the original permission [is_list x 'l] only if you trade
      //the permission [is_list y tl]
    pure (Cons? 'l /\ tl == Cons?.tl 'l)
{
    let np = Some?.v x;
    is_list_case_some x np;
    with node tl. _;
    let nd = !np;
    rewrite each node as nd;
    tail_for_cons np tl;
    nd.tail
}

fn length_iter (#t:Type) (x: llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  let mut cur = x;
  let mut ctr = 0;
  I.refl (is_list x 'l); //initialize the trade for the invariant
  while (
    let v = !cur;
    Some? v
  )
  invariant b.
  exists* n ll suffix.
    pts_to ctr n **
    pts_to cur ll **
    is_list ll suffix **
    pure (n == List.Tot.length 'l - List.Tot.length suffix /\
          b == (Some? ll)) **
    (is_list ll suffix @==> is_list x 'l)
  {
    with _n _ll _suffix. _; //bind existential variables in the invariant
    let n = !ctr;
    let ll = !cur;
    rewrite each _ll as ll; //again, rewrite the context to use ll instead of _ll
    //show_proof_state;
      (* is_list ll suffix @==> is_list x 'l **
         is_list ll suffix
      *)
    let next = tail ll;     //tail gives us back a trade
    //show_proof_state;
      (* is_list ll suffix @==> is_list x 'l **
         (exists* (tl:list t).
            is_list next tl **
            is_list next tl @==> is_list ll suffix **
            pure (Cons? suffix /\ tl == suffix.tl)))
      *)
    with tl. _;
    //show_proof_state;
      (* is_list ll suffix @==> is_list x 'l **
         is_list next tl @==> is_list ll suffix **
         is_list next tl
      *)
    I.trans (is_list next tl) _ _; //extend the trade, transitively
    //show_proof_state;
      (* is_list next tl @==> is_list x 'l **
         is_list next tl
      *)
    cur := next;
    ctr := n + 1;
  };
  with _n ll _sfx. _;
  is_list_case_none ll; //this tells us that suffix=[]; so n == List.Tot.length 'l
  I.elim _ _;           //regain ownership of x, giving up ll
  let n = !ctr;
  n
}

(* Append, Recursively *)

fn rec append (#t:Type0) (x y:llist t)
requires is_list x 'l1 ** is_list y 'l2 ** pure (Some? x)
ensures is_list x ('l1 @ 'l2)
{
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  let node = !np;
  rewrite each _node as node;
  match node.tail {
    None -> {
      //show_proof_state;
        (* R.pts_to np node **
           is_list y 'l2 **
           is_list None tl *)
      is_list_case_none node.tail;
      elim_is_list_nil node.tail;
      //show_proof_state;
        (* pure (node.tail == None) **
           R.pts_to np node **
           is_list y 'l2
         *)
      np := { node with tail = y };
      //show_proof_state;
      rewrite each y as ({ node with tail = y }).tail in (is_list y 'l2);
      //show_proof_state;
      intro_is_list_cons x np;
      //show_proof_state;
    }
    Some _ -> {
      append node.tail y;
      intro_is_list_cons x np;
    }
  }
}