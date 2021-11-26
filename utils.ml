
let list_to_seq l =
  List.fold_right Seq.cons l Seq.empty

let seq_to_list s =
  let l =
    Seq.fold_left (fun a b -> b :: a) [] s in
  List.rev l

let list_find_opt f l =
  List.fold_left (fun a b -> if f b then Some b else a) None l


let list_remove_duplicate (type a) (comp : a -> a -> int) (l : a list) =
  let module TSet = Set.Make(struct
      type t = a
      let compare = comp
    end
  ) in
  let set = TSet.of_list l in
  TSet.fold List.cons set []

let warn s =
  print_string @@ "Warning: " ^ s

let tell l_r e =
  l_r := e :: ! l_r
