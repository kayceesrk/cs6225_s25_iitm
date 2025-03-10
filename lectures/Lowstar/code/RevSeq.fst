module RevSeq

open FStar.List.Tot
open FStar.Seq

let rec rev_list l =
  match l with
  | [] -> []
  | h::t -> rev_list t @ [h]

val swap : #a:eqtype -> s:seq a -> i:nat{i < Seq.length s} -> j:nat{j < Seq.length s} -> seq a
let swap s i j =
  let ei = Seq.index s i in
  let ej = Seq.index s j in
  let s' = Seq.upd s i ej in
  Seq.upd s' j ei

val rev_seq' : #a:eqtype -> s:seq a -> i:nat{i <= Seq.length s} -> Tot (seq a) (decreases (Seq.length s - i))
let rec rev_seq' s i =
  if i < Seq.length s / 2 then
    let s' = swap s i (Seq.length s - i - 1) in
    rev_seq' s' (i + 1)
  else
    s

let rev_seq s = rev_seq' s 0

val rev_lemma_step : #a:eqtype -> orig:seq a -> cur:seq a -> i:nat ->
  Pure (seq a) (requires
          (let l = Seq.length orig in
            (Seq.length cur = l) /\
            (i < l/2) /\
            (seq_to_list (Seq.slice cur 0 i) = rev_list (seq_to_list (Seq.slice orig (l - i - 1) l))) /\
            (seq_to_list (Seq.slice cur (l - i - 1) l) = rev_list (seq_to_list (Seq.slice orig 0 i))) /\
            (seq_to_list (Seq.slice cur i (l - i)) = seq_to_list (Seq.slice orig i (l - i)))))
        (ensures
          (fun cur ->
            let l = Seq.length orig in
            (Seq.length cur = l) /\
            (seq_to_list (Seq.slice cur 0 (i+1)) = rev_list (seq_to_list (Seq.slice orig (l - i - 2) l))) /\
            (seq_to_list (Seq.slice cur (l - i - 2) l) = rev_list (seq_to_list (Seq.slice orig 0 (i+1)))) /\
            (seq_to_list (Seq.slice cur (i+1) (l - i - 1)) = seq_to_list (Seq.slice orig (i+1) (l - i - 1)))))
let rev_lemma_step orig cur i =
  let ei = Seq.index cur i in
  let ei' = Seq.index cur (Seq.length cur - i - 1) in
  let cur' = Seq.upd cur i ei' in
  let cur'' = Seq.upd cur' (Seq.length cur - i - 1) ei in
  let res = cur'' in
  let l = Seq.length orig in
  assert (Seq.length cur'' = l);
  cur''



val rev_lemma : #a:eqtype -> s:seq a -> Tot (rev_list (seq_to_list s) = seq_to_list (rev_seq s))
let rev_lemma s = admit ()