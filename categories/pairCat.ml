open Lib2

module Cat = struct
  type obj_t = L | R | P
  type arr_t = PiL | PiR

  let obj_to_name = function
    | L -> "L"
    | R -> "R"
    | P -> "P"

  let arr_to_name = function
    | PiL -> "piL"
    | PiR -> "piR"

  let src = function
    | PiL -> L
    | PiR -> R

  let tgt = function
    | PiL -> P
    | PiR -> P

  type path' =
    | PathOne of arr_t
    | PathSucc of (arr_t * path')

  type path =
    | PathId of obj_t
    | PathMult of path'

  let objects = [L;R;P]
  let arrows = [PiL;PiR]

  let equations = []
end

module Ps = Presheaf (Cat)

let l = Ps.SGen.fresh_gen "l"
let r = Ps.SGen.fresh_gen "r"

let l' = Ps.SGen.fresh_gen "l'"
let r' = Ps.SGen.fresh_gen "r'"
let c = Ps.SGen.fresh_gen "c"

let psA =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.L l;
  Ps.add_el' p Cat.R r;
  p

let psB =
  let p = Ps.ps_empty' () in
  Ps.add_el' p Cat.L l';
  Ps.add_el' p Cat.R r';
  Ps.add_el' p Cat.P c;
  Ps.add_map' p Cat.PiL c l';
  Ps.add_map' p Cat.PiR c r';
  p

let psF =
  let m = Ps.morph_empty () in
  Ps.morph_add m Cat.L l l';
  Ps.morph_add m Cat.R r r';
  m

let ortho_maps = [(psA,psB,psF)]
