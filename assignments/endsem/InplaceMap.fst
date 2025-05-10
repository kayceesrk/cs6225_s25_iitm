module InplaceMap
#lang-pulse
open Pulse
open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open FStar.SizeT
open Pulse.Lib.BoundedIntegers

fn map_inplace (#t:Type0) (l:SZ.t) (f:t->t) (a:array t) (#s:erased (Seq.seq t))
requires
  pts_to a s ** pure (True) //complete this spec
ensures
  exists* s'.
    pts_to a s' ** pure (True) //complete this spec
{
  admit ();
}