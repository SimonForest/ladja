open Lib2

module Cat = struct

  type obj_t = C0 | C1 | C12
  type arr_t = Dminus | Dplus | Id | Comp | PiL | PiR

  type path' =
  | PathOne of arr_t
  | PathSucc of (arr_t * path')

  type path =
    PathId of obj_t
  | PathMult of path'

  let src = function
    | Dminus -> C0
    | Dplus -> C0
    | Id -> C1
    | Comp -> C1
    | PiL -> C1
    | PiR -> C1

  let tgt = function
    | Dminus -> C1
    | Dplus -> C1
    | Id -> C0
    | Comp -> C12
    | PiL -> C12
    | PiR -> C12

  let objects = [C0 ; C1 ; C12]
  let arrows = [Dminus ; Dplus ; Id ; Comp ; PiL ; PiR]

  let rec list_to_path' = function
    | [a] -> PathOne a
    | a :: q -> PathSucc (a,list_to_path' q)
    | _ -> failwith "Unexpected case."

  let list_to_path l = PathMult (list_to_path' l)

  let object_to_path o = PathId o

  let equations = [
    (object_to_path C0,list_to_path [Dminus;Id]);
    (object_to_path C0,list_to_path [Dplus;Id]);
    (list_to_path [Dminus;PiL],list_to_path [Dminus;Comp]);
    (list_to_path [Dplus;PiR],list_to_path [Dplus;Comp]);
    (list_to_path [Dminus;PiR],list_to_path [Dplus;PiL])
  ]
  (*NOTE: here, if we inverse the members of the equation, we get a rather long
     element name when we build the free ps on one element. The privileged
     element is indeed the one on the left. So one must carefully orient the
     equations for the simplicity of names at least. *)

  let obj_to_name = function
    | C0 -> "C0"
    | C1 -> "C1"
    | C12 -> "C12"

  let arr_to_name = function
    | Id -> "id"
    | Dminus -> "d-"
    | Dplus -> "d+"
    | Comp -> "comp"
    | PiL -> "pi1"
    | PiR -> "pi2"

end

module Ps = Presheaf(Cat)

let l = Ps.SGen.fresh_gen "l"
let r = Ps.SGen.fresh_gen "r"
let y = Ps.SGen.fresh_gen "y"
let l' = Ps.SGen.fresh_gen "l'"
let r' = Ps.SGen.fresh_gen "r'"
let y' = Ps.SGen.fresh_gen "y'"
let c = Ps.SGen.fresh_gen "c"

let psA =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C1 l;
  Ps.add_el' p Cat.C1 r;
  Ps.add_el' p Cat.C0 y;
  Ps.add_map' p Cat.Dplus l y;
  Ps.add_map' p Cat.Dminus r y;
  p

let psB =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C1 l';
  Ps.add_el' p Cat.C1 r';
  Ps.add_el' p Cat.C12 c;
  Ps.add_el' p Cat.C0 y';
  Ps.add_map' p Cat.Dplus l' y';
  Ps.add_map' p Cat.Dminus r' y';
  Ps.add_map' p Cat.PiL c l';
  Ps.add_map' p Cat.PiR c r';
  p

let psf =
  let m = Ps.morph_empty () in
  Ps.morph_add m Cat.C1 l l';
  Ps.morph_add m Cat.C1 r r';
  Ps.morph_add m Cat.C0 y y';
  m

let o_pair = (psA,psB,psf)

let x = Ps.SGen.fresh_gen "x"
let y = Ps.SGen.fresh_gen "y"
let idx = Ps.SGen.fresh_gen "x;id"
let idy = Ps.SGen.fresh_gen "y;id"
let a = Ps.SGen.fresh_gen "a"
let b = Ps.SGen.fresh_gen "b"
let idxb = Ps.SGen.fresh_gen "(idx,b)"
let aidy = Ps.SGen.fresh_gen "(a,idy)"
let compa = Ps.SGen.fresh_gen "a*idy"
let compb = Ps.SGen.fresh_gen "idx*b"

let psA =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C0 x;
  (* Ps.add_el' p Cat.C0 y; *)
  Ps.add_el' p Cat.C1 idx;
  Ps.add_el' p Cat.C1 b;
  Ps.add_el' p Cat.C1 compb;
  Ps.add_el' p Cat.C12 idxb;
  Ps.add_map' p Cat.Id x idx;
  Ps.add_map' p Cat.Dminus b x;
  (* Ps.add_map' p Cat.Dplus b y; *)
  Ps.add_map' p Cat.PiL idxb idx;
  Ps.add_map' p Cat.PiR idxb b;
  Ps.add_map' p Cat.Comp idxb compb;
  p

let psB =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C0 x;
  (* Ps.add_el' p Cat.C0 y; *)
  Ps.add_el' p Cat.C1 idx;
  Ps.add_el' p Cat.C1 b;
  Ps.add_el' p Cat.C12 idxb;
  Ps.add_map' p Cat.Id x idx;
  Ps.add_map' p Cat.Dminus b x;
  (* Ps.add_map' p Cat.Dplus b y; *)
  Ps.add_map' p Cat.PiL idxb idx;
  Ps.add_map' p Cat.PiR idxb b;
  Ps.add_map' p Cat.Comp idxb b;
  p

let psf =
  let m = Ps.morph_empty () in
  Ps.morph_add m Cat.C0 x x;
  Ps.morph_add m Cat.C1 idx idx;
  Ps.morph_add m Cat.C1 b b;
  Ps.morph_add m Cat.C1 compb b;
  Ps.morph_add m Cat.C12 idxb idxb;
  m

let o_unitl = (psA,psB,psf)

let psA =
  let p = Ps.ps_empty' () in
  (* Ps.add_el' p Cat.C0 x; *)
  Ps.add_el' p Cat.C0 y;
  Ps.add_el' p Cat.C1 idy;
  Ps.add_el' p Cat.C1 a;
  Ps.add_el' p Cat.C1 compa;
  Ps.add_el' p Cat.C12 aidy;
  Ps.add_map' p Cat.Id y idy;
  Ps.add_map' p Cat.Dplus a y;
  (* Ps.add_map' p Cat.Dplus b y; *)
  Ps.add_map' p Cat.PiL aidy a;
  Ps.add_map' p Cat.PiR aidy idy;
  Ps.add_map' p Cat.Comp aidy compa;
  p

let psB =
  let p = Ps.ps_empty' () in
  (* Ps.add_el' p Cat.C0 x; *)
  Ps.add_el' p Cat.C0 y;
  Ps.add_el' p Cat.C1 idy;
  Ps.add_el' p Cat.C1 a;
  Ps.add_el' p Cat.C12 aidy;
  Ps.add_map' p Cat.Id y idy;
  Ps.add_map' p Cat.Dplus a y;
  (* Ps.add_map' p Cat.Dplus b y; *)
  Ps.add_map' p Cat.PiL aidy a;
  Ps.add_map' p Cat.PiR aidy idy;
  Ps.add_map' p Cat.Comp aidy a;
  p

let psf =
  let m = Ps.morph_empty () in
  Ps.morph_add m Cat.C0 y y;
  Ps.morph_add m Cat.C1 idy idy;
  Ps.morph_add m Cat.C1 a a;
  Ps.morph_add m Cat.C1 compa a;
  Ps.morph_add m Cat.C12 aidy aidy;
  m

let o_unitr = (psA,psB,psf)

let a = Ps.SGen.fresh_gen "a"
let b = Ps.SGen.fresh_gen "b"
let c = Ps.SGen.fresh_gen "c"
let pab = Ps.SGen.fresh_gen "(a,b)"
let pbc = Ps.SGen.fresh_gen "(b,c)"
let cab = Ps.SGen.fresh_gen "a*b"
let cbc = Ps.SGen.fresh_gen "b*c"
let pcabc= Ps.SGen.fresh_gen "(a*b,c)"
let pacbc= Ps.SGen.fresh_gen "(a,b*c)"

let a' = Ps.SGen.fresh_gen "a"
let b' = Ps.SGen.fresh_gen "b"
let c' = Ps.SGen.fresh_gen "c"
let pab' = Ps.SGen.fresh_gen "(a,b)"
let pbc' = Ps.SGen.fresh_gen "(b,c)"
let cab' = Ps.SGen.fresh_gen "a*b"
let cbc' = Ps.SGen.fresh_gen "b*c"
let pcabc'= Ps.SGen.fresh_gen "(a*b,c)"
let pacbc'= Ps.SGen.fresh_gen "(a,b*c)"
let cabc' = Ps.SGen.fresh_gen "a*b*c"

let psA =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C1 a;
  Ps.add_el' p Cat.C1 b;
  Ps.add_el' p Cat.C1 c;
  Ps.add_el' p Cat.C12 pab;
  Ps.add_map' p Cat.PiL pab a;
  Ps.add_map' p Cat.PiR pab b;
  Ps.add_el' p Cat.C12 pbc;
  Ps.add_map' p Cat.PiL pbc b;
  Ps.add_map' p Cat.PiR pbc c;
  Ps.add_el' p Cat.C1 cab;
  Ps.add_map' p Cat.Comp pab cab;
  Ps.add_el' p Cat.C1 cbc;
  Ps.add_map' p Cat.Comp pbc cbc;
  Ps.add_el' p Cat.C12 pcabc;
  Ps.add_map' p Cat.PiL pcabc cab;
  Ps.add_map' p Cat.PiR pcabc c;
  Ps.add_el' p Cat.C12 pacbc;
  Ps.add_map' p Cat.PiL pacbc a;
  Ps.add_map' p Cat.PiR pacbc cbc;
  p

let psB =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.C1 a';
  Ps.add_el' p Cat.C1 b';
  Ps.add_el' p Cat.C1 c';
  Ps.add_el' p Cat.C12 pab';
  Ps.add_map' p Cat.PiL pab' a';
  Ps.add_map' p Cat.PiR pab' b';
  Ps.add_el' p Cat.C12 pbc';
  Ps.add_map' p Cat.PiL pbc' b';
  Ps.add_map' p Cat.PiR pbc' c';
  Ps.add_el' p Cat.C1 cab';
  Ps.add_map' p Cat.Comp pab' cab';
  Ps.add_el' p Cat.C1 cbc';
  Ps.add_map' p Cat.Comp pbc' cbc';
  Ps.add_el' p Cat.C12 pcabc';
  Ps.add_map' p Cat.PiL pcabc' cab';
  Ps.add_map' p Cat.PiR pcabc' c';
  Ps.add_el' p Cat.C12 pacbc';
  Ps.add_map' p Cat.PiL pacbc' a';
  Ps.add_map' p Cat.PiR pacbc' cbc';
  Ps.add_el' p Cat.C1 cabc';
  Ps.add_map' p Cat.Comp pcabc' cabc';
  Ps.add_map' p Cat.Comp pacbc' cabc';
  p

let psf =
  let m = Ps.morph_empty () in
  Ps.morph_add m Cat.C1 a a';
  Ps.morph_add m Cat.C1 b b';
  Ps.morph_add m Cat.C1 c c';
  Ps.morph_add m Cat.C12 pab pab';
  Ps.morph_add m Cat.C12 pbc pbc';
  Ps.morph_add m Cat.C1 cab cab';
  Ps.morph_add m Cat.C1 cbc cbc';
  Ps.morph_add m Cat.C12 pcabc pcabc';
  Ps.morph_add m Cat.C12 pacbc pacbc';
  m

let o_assoc = (psA,psB,psf)

let ortho_maps = [o_pair;o_unitl;o_unitr;o_assoc]
