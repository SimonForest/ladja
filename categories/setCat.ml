open Lib2
module Cat = struct
  type obj_t = Ast
  type arr_t = |

  let obj_to_name = function
    | Ast -> "0"

  let arr_to_name : arr_t -> string = function
    | _ -> .

  let src : arr_t -> obj_t = function
    | _ -> .

  let tgt : arr_t -> obj_t = function
    | _ -> .

  type path' =
    | PathOne of arr_t
    | PathSucc of (arr_t * path')

  type path =
    | PathId of obj_t
    | PathMult of path'

  let objects = [Ast]
  let arrows = []
  let equations = []
end

module Ps = Presheaf (Cat)

let ortho_maps : (Ps.t' * Ps.t' * Ps.morph) list = []
