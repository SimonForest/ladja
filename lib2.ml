
let fpf =
  Format.printf

module type OrdNamedType = sig
  type t
  val compare : t -> t -> int
    (* TODO: the following should be removed for AGen and OGen *)
  val to_name : t -> string
end

module type OrdNamedInstType = sig
  include OrdNamedType
  val fresh_gen : string -> t
end

module type OrdNamedInstPriorityType = sig
  include OrdNamedInstType
  val fresh_gen_with_priority : string -> int -> t
  val get_priority : t -> int
end

module type Category = sig
  type obj_t
  type arr_t

  type path' =
  | PathOne of arr_t
  | PathSucc of (arr_t * path')

  type path =
    PathId of obj_t
  | PathMult of path'

  val objects : obj_t list
  val arrows : arr_t list
  val obj_to_name : obj_t -> string
  val arr_to_name : arr_t -> string
  val equations : (path * path) list
  val src : arr_t -> obj_t
  val tgt : arr_t -> obj_t
end

module type CatLibS = sig
  (* module Cat : Category *) (* not sure this field is useful *)
  include Category
  module OGen :
  sig
    type t = obj_t
    val compare : t -> t -> int
    val to_name : t -> string
  end
  module AGen :
  sig
    type t = arr_t
    val compare : t -> t -> int
    val to_name : t -> string
  end
  val psrc : path -> obj_t
  val ptgt : path -> obj_t
  val arr_from : obj_t -> arr_t list
  val arr_to : obj_t -> arr_t list
  (* module OGen :
   * sig
   *   type t = Cat.obj_t
   *   val compare : t -> t -> int
   *   val to_name : t -> string
   * end
   * module AGen :
   * sig
   *   type t = Cat.arr_t
   *   val compare : t -> t -> int
   *   val to_name : t -> string
   * end
   * val psrc : Cat.path -> Cat.obj_t
   * val ptgt : Cat.path -> Cat.obj_t
   * val arr_from : Cat.obj_t -> Cat.arr_t list
   * val arr_to : Cat.obj_t -> Cat.arr_t list *)
end

module CatLib (C : Category) : CatLibS
  with
    type obj_t = C.obj_t and type arr_t = C.arr_t
                         and type path' = C.path'
                         and type path = C.path
=
struct
  include C
  module OGen = struct
    type t = C.obj_t
    let compare = compare
    let to_name = C.obj_to_name
  end
  module AGen = struct
    type t = C.arr_t
    let compare = compare
    let to_name = C.arr_to_name
  end
  let psrc' = function
    | C.PathOne a -> C.src a
    | C.PathSucc (a,p') -> C.src a
  let psrc = function
    | C.PathId o -> o
    | C.PathMult p' -> psrc' p'
  let rec ptgt' = function
    | C.PathOne a -> C.tgt a
    | C.PathSucc (a,p') -> ptgt' p'
  let ptgt = function
    | C.PathId o -> o
    | C.PathMult p' -> ptgt' p'

  let arr_from =
    let module OMap = Map.Make (struct
        type t = C.obj_t
        let compare = compare
      end)
    in
    let omap = ref OMap.empty in
    List.iter
      (fun o ->
         omap := OMap.add o [] !omap
      )
      C.objects ;
    List.iter
      (fun arr ->
         let o = C.src arr in
         let old = OMap.find o !omap in
         omap := OMap.add o (arr :: old) !omap
      )
      C.arrows ;
    fun o -> OMap.find o !omap

  let arr_to =
    let module OMap = Map.Make (struct
        type t = C.obj_t
        let compare = compare
      end)
    in
    let omap = ref OMap.empty in
    List.iter
      (fun o ->
         omap := OMap.add o [] !omap
      )
      C.objects ;
    List.iter
      (fun arr ->
         let o = C.tgt arr in
         let old = OMap.find o !omap in
         omap := OMap.add o (arr :: old) !omap
      )
      C.arrows ;
    fun o -> OMap.find o !omap
end

module Op (C : Category) : Category with
    type obj_t = C.obj_t and type arr_t = C.arr_t
                         and type path' = C.path'
                         and type path = C.path
= struct
  type obj_t = C.obj_t
  type arr_t = C.arr_t

  type path' = C.path' =
             |PathOne of arr_t
             | PathSucc of (arr_t * path')

  type path = C.path = PathId of obj_t | PathMult of path'

  let objects = C.objects
  let arrows = C.arrows

  let rec inv_path' res = function
    | C.PathOne a -> C.PathSucc (a,res)
    | C.PathSucc (a,p) -> inv_path' (C.PathSucc (a,res)) p

  let inv_path = function
    | C.PathMult p' ->
      begin
        match p' with
        | C.PathSucc (a,p'') -> C.PathMult (inv_path' (C.PathOne a) p'')
        | C.PathOne a -> PathMult (C.PathOne a)
      end
    | C.PathId o -> C.PathId o

  let equations =
    List.map
      (fun (l,r) -> (inv_path l,inv_path r))
      C.equations
  let obj_to_name = C.obj_to_name
  let arr_to_name = C.arr_to_name
  let src = C.tgt
  let tgt = C.src
end

module type PresheafT = sig
  module C : Category
  module Cop :
  sig
    type obj_t = Op(C).obj_t
    type arr_t = Op(C).arr_t
    type path' =
        Op(C).path' =
        PathOne of arr_t
      | PathSucc of (arr_t * path')
    type path = Op(C).path = PathId of obj_t | PathMult of path'
    val objects : obj_t list
    val obj_to_name : obj_t -> string
    val arr_to_name : arr_t -> string
    val arrows : arr_t list
    val equations : (path * path) list
    val src : arr_t -> obj_t
    val tgt : arr_t -> obj_t
    module OGen :
    sig
      type t = obj_t
      val compare : t -> t -> int
      val to_name : t -> string
    end
    module AGen :
    sig
      type t = arr_t
      val compare : t -> t -> int
      val to_name : t -> string
    end
    val psrc : path -> obj_t
    val ptgt : path -> obj_t
    val arr_from : obj_t -> arr_t list
    val arr_to : obj_t -> arr_t list
  end
  type sgen
  val fresh : unit -> int
  module SGen : OrdNamedInstPriorityType
  type t
  type t'
  val ps_empty' : unit -> t'
  val ps_foreach_oelt : t' -> (Cop.OGen.t * SGen.t -> unit) -> unit
  val ps_foreach_map :
    t' -> (SGen.t * Cop.AGen.t * SGen.t -> unit) -> unit
  val print_ps_elts' : t' -> unit
  val print_ps_maps' : t' -> unit
  type morph
  val morph_empty : unit -> morph
  val morph_add : morph -> Cop.OGen.t -> SGen.t -> SGen.t -> unit
  val morph_domain : morph -> Set.Make(SGen).t
  val morph_codomain : morph -> Set.Make(SGen).t
  val morph_normalize : morph -> unit
  val morph_from_map : (Cop.OGen.t * SGen.t * SGen.t) list -> morph
  val morph_to_map : morph -> (Cop.OGen.t * SGen.t * SGen.t) list
  val print_morph : morph -> unit
  val morph_img : morph -> SGen.t -> SGen.t
  val morph_img_opt : morph -> Cop.OGen.t -> SGen.t -> SGen.t option
  val morph_is_iso : t' -> t' -> morph -> bool
  val morph_is_epi : t' -> t' -> morph -> bool
  type ctxt
  val create_ctxt : t' -> ctxt
  val ctxt_incr_rev : ctxt -> unit
  val ctxt_get_rev : ctxt -> int
  val ctxt_get_rep : ctxt -> Cop.OGen.t -> SGen.t -> SGen.t
  val ctxt_set_new_rep : ctxt -> Cop.OGen.t -> SGen.t -> SGen.t -> unit
  val ctxt_result :
    ctxt -> t' * morph
  val ctxt_get_ps : ctxt -> t'
  val obj_to_set : t -> Cop.obj_t -> Set.Make(SGen).t
  val arr_to_map : t -> Cop.AGen.t -> SGen.t -> SGen.t
  val arr_to_map_opt : t -> Cop.AGen.t -> SGen.t -> SGen.t option
  val arr_to_map' : t' -> C.arr_t -> SGen.t -> SGen.t * C.arr_t * SGen.t
  val arr_to_map_opt' :
    t' -> Cop.AGen.t -> SGen.t -> (SGen.t * Cop.AGen.t * SGen.t) option
  val path'_to_map : t -> Cop.path' -> SGen.t -> SGen.t
  val path_to_map : t -> Cop.path -> SGen.t -> SGen.t
  val add_el : t -> Cop.OGen.t -> SGen.t -> unit
  val add_el' : t' -> Cop.OGen.t -> SGen.t -> unit
  val ctxt_add_el' : ctxt -> Cop.OGen.t -> SGen.t -> unit
  val compute_oelt_pairs : t' -> (Cop.obj_t * SGen.t) list
  val remove_elt_stupid' : t' -> Cop.obj_t -> SGen.t list -> unit
  val remove_elt_stupid : t' -> Cop.obj_t -> SGen.t -> unit
  val add_map : t -> Cop.AGen.t -> SGen.t -> SGen.t -> unit
  val add_map' : t' -> Cop.AGen.t -> SGen.t -> SGen.t -> unit
  val ctxt_add_map' : ctxt -> Cop.AGen.t -> SGen.t -> SGen.t -> unit
  val compute_yoneda_obj : Cop.OGen.t -> t'
  val equalize_elts' :
    t' -> Cop.obj_t -> SGen.t -> SGen.t list -> unit
  val ctxt_equalize_elts' :
    ctxt -> Cop.OGen.t -> SGen.t -> SGen.t list -> unit
  val equalize_elts : t' -> Cop.obj_t -> SGen.t -> SGen.t -> unit
  val ctxt_equalize_elts : ctxt -> Cop.OGen.t -> SGen.t -> SGen.t -> unit
  val compute_pairs_equalization :
    t' ->
    (Cop.obj_t * SGen.t * SGen.t) list ->
    (Cop.obj_t * SGen.t * SGen.t) list ref
  val find_parallel_maps :
    t' -> ((SGen.t * Cop.AGen.t) * SGen.t list) list
  val ctxt_find_parallel_maps :
    ctxt -> ((SGen.t * Cop.AGen.t) * SGen.t list) list
  val enforce_many_to_one : t' -> bool
  val ctxt_enforce_many_to_one : ctxt -> unit
  val compute_equation_pairs :
    t' -> Cop.path * Cop.path -> (Cop.obj_t * SGen.t * SGen.t) list
  val ctxt_compute_equation_pairs :
    ctxt -> Cop.path * Cop.path -> (Cop.obj_t * SGen.t * SGen.t) list
  val compute_equations_pairs :
    t' ->
    (Cop.path * Cop.path) list -> (Cop.obj_t * SGen.t * SGen.t) list
  val ctxt_compute_equations_pairs :
    ctxt ->
    (Cop.path * Cop.path) list -> (Cop.obj_t * SGen.t * SGen.t) list
  val enforce_equations_one_step : t' -> bool
  val morph_expand : t' -> t' -> morph -> morph
  val ctxt_enforce_equations_one_step : ctxt -> unit
  val expand_presheaf_stupid : t -> 'a
  val expand_presheaf_naive : t -> unit
  val expand_presheaf_one_step : t' -> (Cop.obj_t * SGen.t) list
  val ctxt_expand_presheaf_one_step : ctxt -> unit
  val expand_presheaf_interleaved : t' -> bool
  val ctxt_presheaf_interleaved : ctxt -> unit
  val check_morph' :
    t' -> t' -> (Cop.OGen.t * SGen.t * SGen.t) list -> bool
  val compute_inv_maps : 'a -> 'b -> morph -> ((Cop.obj_t * SGen.t) * SGen.t list) list
  val compute_ps_liftings :
    t' ->
    t' ->
    morph ->
    t' -> morph -> morph list
  val compute_ps_morphs :
    t' -> t' -> morph list
  val ps_make_renamed_copy :
    t' ->
    (Cop.obj_t -> SGen.t -> string) ->
    t' * morph
  val morph_comp :
    morph -> morph -> morph
  val morph_comp_with_partial_r :
    morph -> morph -> morph
  val ps_add_unify_construction :
    t' ->
    (Cop.OGen.t * SGen.t) list ->
    (Cop.AGen.t * SGen.t * SGen.t) list ->
    (Cop.obj_t * SGen.t * SGen.t) list -> t' * morph
  val ctxt_add_unify_construction :
    ctxt ->
    (Cop.OGen.t * SGen.t) list ->
    (Cop.AGen.t * SGen.t * SGen.t) list ->
    (Cop.OGen.t * SGen.t * SGen.t) list -> unit
  val ctxt_add_ps_copy : ctxt -> t' -> morph
  val enforce_ex_lifting_step :
    (t' * t' * morph) list -> t' -> t' * morph
  val ctxt_enforce_ex_lifting_step :
    (t' * t' * morph) list -> ctxt -> unit
  val enforce_unique_lifting_step :
    (t' * t' * morph) list -> t' -> t' * morph
  val ctxt_enforce_unique_lifting_step :
    (t' * t' * morph) list -> ctxt -> unit
  val ctxt_compute_ortho : (t' * t' * morph) list -> ctxt -> unit
  val ctxt_compute_ortho_map :
    (t' * t' * morph) list ->
    ctxt -> ctxt -> morph -> morph

  type prod_res
  val prod_res_get_ps : prod_res -> t'
  val compute_prod : t' -> t' -> prod_res

  val compute_prod_map_r : t' -> t' -> 'a -> morph ->
    prod_res -> prod_res -> morph
end

module Presheaf (C : Category) (* : PresheafT with module C = C *) = struct
  (* TODO: uncomment ^ when the code is finalized. *)
  module C = C
  module Cop = CatLib (Op (C))
  type sgen = { id : int ; name : string ; priority : int }
  (* priority is useful to prioritize some elements in order to compute
     morphisms from one presheaf to another. *)

  let fresh = let r = ref 0 in
    fun () -> (incr r; !r)

  module SGen = struct
    type t = sgen
    let compare = compare
    let fresh_gen name = { id = fresh () ; name = name ; priority = -1 }
    let to_name sgen = sgen.name
    let fresh_gen_with_priority name priority =
      { id = fresh () ; name = name ; priority = priority }
    let get_priority sgen = sgen.priority
  end

  let compare_with_priority l r =
    match l.priority,r.priority with
    | (-1,-1) -> 0
    | (-1,_) -> 1
    | (_,-1) -> -1
    | (a,b) when a < b -> -1
    | _ -> 1

  module SSet = Set.Make(SGen)

  module OMap = Map.Make(Cop.OGen)

  module AEMap = Map.Make(struct
      type t = Cop.AGen.t * SGen.t
      let compare (a,s) (a',s') = let r = Cop.AGen.compare a a' in
        if r <> 0 then r else compare s s'
    end)

  type t =  { elts : SSet.t OMap.t ref ; maps : SGen.t AEMap.t ref }

  (* more adequate type for the intermediate constructions *)
  (*TODO: maps should be a set. Otherwise, it can induce bugs here and there.*)
  type t' = { elts : SSet.t OMap.t ref ; maps :  SGen.t list AEMap.t ref ; inv_maps : SGen.t list AEMap.t ref }

  let ps_empty' () =
    {
      elts = ref OMap.empty ;
      maps = ref AEMap.empty;
      inv_maps = ref AEMap.empty
    }

  let ps_foreach_oelt (ps : t') (f : (Cop.OGen.t * SGen.t) -> unit) =
    OMap.iter
      (fun o s ->
         SSet.iter
           (fun el -> f (o,el))
           s
      )
      !(ps.elts)

  let ps_foreach_map (ps : t') (f : (SGen.t * Cop.AGen.t * SGen.t) -> unit) =
    AEMap.iter (fun (arr,el_s) l ->
        List.iter (fun el_t -> f (el_s,arr,el_t)) l
      )
      !(ps.maps)

  let arr_to_map (ps : t) arr el =
    AEMap.find (arr,el) !(ps.maps)

  let arr_to_map_opt (ps : t) arr el =
    AEMap.find_opt (arr,el) !(ps.maps)

  let arr_to_map' (ps : t') arr el =
    match AEMap.find (arr,el) !(ps.maps) with
    | [] -> failwith "no image for a map."
    | el_t :: q -> el_t

  let arr_to_map_opt' (ps : t') arr el =
    match AEMap.find_opt (arr,el) !(ps.maps) with
    | Some (el_t :: _) -> Some el_t
    | _ -> None

  let print_ps_elts' (ps : t') =
    let oelts = OMap.bindings !(ps.elts) in
    Format.printf "@[<v 0>[@[<v 2>";
    List.iter (fun (o,s) ->
        SSet.iter (fun el ->
            Format.printf "@,%s : %s" (SGen.to_name el) (Cop.OGen.to_name o)
          )
          s
      )
      oelts
    ;
    Format.printf "@]@,]@,@]"

  let print_ps_maps' (ps : t') =
    Format.printf "@[<v 0>[@[<v 2>";
    ps_foreach_map ps
      (fun (els,arr,elt) ->
         Format.printf "@,%s(%s) = %s" (Cop.AGen.to_name arr) (SGen.to_name els) (SGen.to_name elt)
      ) ;
    Format.printf "@]@,]@,@]"

  module OSMap = Map.Make(struct
      type t = Cop.OGen.t * SGen.t
      let compare = compare
    end)

  (* MORPHISMES *)
  type morph = (Cop.OGen.t * SGen.t * SGen.t) list ref

  let morph_empty () = ref []

  let morph_add (m : morph) o s t =
    m := (o,s,t) :: !m

  let morph_domain m =
    let res = ref SSet.empty in
    List.iter
      (fun (o,s,t) ->
         res := SSet.add s !res
      )
      !m ;
    !res

  let morph_codomain m =
    let res = ref SSet.empty in
    List.iter
      (fun (o,s,t) ->
         res := SSet.add t !res
      )
      !m ;
    !res

  let morph_normalize m =
    let module OSSSet = Set.Make (struct
        type t = Cop.OGen.t * SGen.t * SGen.t
        let compare = compare
      end
      ) in
    let s = OSSSet.of_list !m in
    m := Utils.seq_to_list @@ OSSSet.to_seq s

  let morph_from_map map : morph = ref map (* (Cop.OGen.t * SGen.t * SGen.t) list -> morph*)

  let morph_to_map m : (Cop.OGen.t * SGen.t * SGen.t) list = !m

  let print_morph (m : morph) =
    let binds = !m in
    Format.printf "@[<v 0>[@[<v 2>";
    List.iter (fun (o,s,t) ->
        Format.printf "@,%s -> %s : %s" (SGen.to_name s) (SGen.to_name t) (Cop.OGen.to_name o)
      )
      binds ;
    Format.printf "@]@,]@,@]"

  (* compute the image of an element by a ps morphism. *)
  let morph_img m x =
    let (_,_,y) = List.find (fun (o,x',y) -> x = x') !m in
    y

  let morph_img_opt m o x =
    Option.bind
      (Utils.list_find_opt (fun (o,x',y) -> x = x') !m)
      (fun (_,_,y) -> Some y)

  let morph_is_iso (psA : t') (psB : t') (mF : morph) : bool =
    try
      let imgs = ref SSet.empty in
      ps_foreach_oelt psA
        (fun (o,elA) ->
           let elB = morph_img mF elA in
           if SSet.mem elB !imgs then
             raise Exit;
           imgs := SSet.add elB !imgs
        ) ;
      ps_foreach_oelt psB
        (fun (o,elB) ->
           if not @@ SSet.mem elB !imgs then
             raise Exit
        );
      true
    with
    | Exit -> false


  (** Tell whether a morphism is a weak epi, in the sense that every element of
     B is below an element in the image of F. *)
  (* TODO: add the check that every map in B is image of one in A. Otherwise,
     the simplification for weak epi orth morphism will not be correct. *)
  (* let morph_is_weak_epi (psA : t') (psB : t') (mF : morph) : bool =
   *   let imgs = ref [] in
   *   ps_foreach_oelt psA
   *     (fun (o,elA) ->
   *        let elB = morph_img mF elA in
   *        imgs := (o,elB) :: !imgs
   *     ) ;
   *   let done_els = ref SSet.empty in
   *   let rec aux = function
   *     | [] ->
   *       begin
   *         let objBs = ref SSet.empty in
   *         ps_foreach_oelt psB (fun (o,elB) ->
   *             objBs := SSet.add elB !objBs
   *           );
   *         if SSet.is_empty (SSet.diff !objBs !done_els) then
   *           true
   *         else
   *           false
   *       end
   *     | (o,elB) :: q when SSet.mem elB !done_els -> aux q
   *     | (o,elB) :: q ->
   *       begin
   *         done_els := SSet.add elB !done_els;
   *         let arrs = Cop.arr_from o in
   *         let next = ref q in
   *         List.iter
   *           (fun arr ->
   *              let o_target = Cop.tgt arr in
   *              match arr_to_map_opt' psB arr elB with
   *              | None -> ()
   *              | Some (_,_,other_elB) -> next := (o_target,other_elB) :: !next
   *           )
   *           arrs;
   *         aux !next
   *       end
   *   in
   *   aux !imgs *)

  let morph_is_epi (psA : t') (psB : t') (mF : morph) : bool =
    let imgs = ref SSet.empty in
    ps_foreach_oelt psA
      (fun (o,elA) ->
         let elB = morph_img mF elA in
         imgs := SSet.add elB !imgs
      ) ;
    let objBs = ref SSet.empty in
    ps_foreach_oelt psB (fun (o,elB) ->
        objBs := SSet.add elB !objBs
      );
    let rem = SSet.diff !objBs !imgs in
    SSet.iter (fun el -> fpf "%s, " (SGen.to_name el)) rem;
    if SSet.is_empty (SSet.diff !objBs !imgs) then
      true
    else
      false
        (* TODO: check surjectivity of inner maps otherwise it is wrong! *)

  type ctxt = {
    init_elts : SSet.t OMap.t ; (* the initial elements from which the first presheaf was made of. *)
    reps : SGen.t OSMap.t ref ; (* the current projections for all the elements that appeared at some point in the construction.*)
    (* ^ will be used as a union-find structure. *)
    ps : t' ;
    rev : int ref (* version number, to easily keep track of changes. *)
  }

  (** create a new context from a presheaf. do not make a copy. *)
  let create_ctxt (ps : t') =
    let init_elts = !(ps.elts) in
    let reps = ref OSMap.empty in
    ps_foreach_oelt ps
      (fun (o,el) ->
         reps := OSMap.add (o,el) el !reps
      ) ;
    { init_elts = init_elts ; reps = reps ; ps = ps ; rev = ref 0 }

  let ctxt_incr_rev ctxt =
    incr ctxt.rev

  let ctxt_get_rev ctxt =
    !(ctxt.rev)

  (* find for context reps. *)
  let rec ctxt_get_rep ps o el =
    let res = OSMap.find (o,el) !(ps.reps) in
    let res' = OSMap.find (o,res) !(ps.reps) in
    if res' <> res then
      let res'' = ctxt_get_rep ps o res' in
      ps.reps := OSMap.add (o,el) res'' !(ps.reps) ;
      res''
    else
      res

  (* union for context reps. !!! the new rep must already be in reps. *)
  let rec ctxt_set_new_rep ps o el new_rep =
    let curr_rep = ctxt_get_rep ps o el in
    let new_rep' = ctxt_get_rep ps o new_rep in
    ps.reps := OSMap.add (o,curr_rep) new_rep' !(ps.reps)

  let ctxt_result ctxt =
    let m = morph_empty () in
    List.iter
      (fun (o,s) ->
         SSet.iter
           (fun el ->
              morph_add m o el (ctxt_get_rep ctxt o el)
           )
           s
      )
      @@ OMap.bindings ctxt.init_elts ;
    (ctxt.ps,m)

  let ctxt_get_ps ctxt =
    ctxt.ps

  let obj_to_set (ps : t) o =
    OMap.find o !(ps.elts)

  let rec path'_to_map (ps : t) = function
    Cop.PathOne a -> arr_to_map ps a
    | Cop.PathSucc (a,path) -> (fun x -> arr_to_map ps a (path'_to_map ps path x))

  let path_to_map (ps : t) = function
    Cop.PathId o -> (fun x -> x) (** todo: check that the elements are in the good set *)
    | Cop.PathMult p' -> path'_to_map ps p'

  let rec path'_to_map' (ps : t') = function
    Cop.PathOne a -> arr_to_map' ps a
    | Cop.PathSucc (a,path) -> (fun x -> arr_to_map' ps a (path'_to_map' ps path x))

  let path_to_map' (ps : t') = function
    Cop.PathId o -> (fun x -> x) (** todo: check that the elements are in the good set *)
    | Cop.PathMult p' -> path'_to_map' ps p'

  let rec path'_to_map_opt' (ps : t') = function
    Cop.PathOne a -> arr_to_map_opt' ps a
    | Cop.PathSucc (a,path) ->
      (fun x -> Option.bind (arr_to_map_opt' ps a x) (path'_to_map_opt' ps path))

  let path_to_map_opt' (ps : t') = function
    Cop.PathId o -> (fun x -> Some x) (** TODO: check that the elements are in the good set *)
    | Cop.PathMult p' -> path'_to_map_opt' ps p'

  let add_el (ps : t) (o : Cop.OGen.t) (el : SGen.t) =
    let old_set = match OMap.find_opt o !(ps.elts) with
      | None -> SSet.empty
      | Some s -> s
    in
    let new_set = SSet.add el old_set in
    ps.elts := OMap.add o new_set !(ps.elts)

  let add_el' (ps : t') (o : Cop.OGen.t) (el : SGen.t) =
    let old_set = match OMap.find_opt o !(ps.elts) with
      | None -> SSet.empty
      | Some s -> s
    in
    let new_set = SSet.add el old_set in
    ps.elts := OMap.add o new_set !(ps.elts)

  let elts_of_type (ps : t') (o : Cop.OGen.t) =
    match OMap.find_opt o !(ps.elts) with
    | None -> SSet.empty
    | Some s -> s

  (** add an element to a presheaf in context. !!! the added element must not be
     already present. **)
  let ctxt_add_el' (ctxt : ctxt) (o : Cop.OGen.t) (el : SGen.t) =
    let old_set = match OMap.find_opt o !(ctxt.ps.elts) with
      | None -> SSet.empty
      | Some s -> s
    in
    let new_set = SSet.add el old_set in
    ctxt.ps.elts := OMap.add o new_set !(ctxt.ps.elts) ;
    ctxt.reps := OSMap.add (o,el) el !(ctxt.reps) ;
    ctxt_incr_rev ctxt

  (** transform a list of mappings to a map of (source,arrow) to (list of targets) *)
  let raw_to_assoc_mappings l =
    let res = ref AEMap.empty in
    List.iter (fun (src,arr,tgt) ->
        res := AEMap.update
          (arr,src)
          (function
            | None -> Some tgt
            | u -> (* Utils.warn "The mapping is not *-to-1." ; *) u
              (* TODO: put some warning in this last case: we want to assume that the mapping is *-to-1 *)
          )
          !res
      )
      l;
    !res

  let compute_oelt_pairs (ps : t') =
    let s_list= OMap.bindings !(ps.elts) in
    List.concat @@ List.map
      (fun (o,s) ->
         let res = ref [] in
         SSet.iter
           (fun e -> res := (o,e) :: !res )
           s;
         !res
      )
      s_list

  (** remove an element from the presheaf. Do not try to remove the associated mappings. *)
  let remove_elt_stupid' (ps : t') o els_l =
    let old_set = OMap.find o !(ps.elts) in
    let new_set = SSet.diff old_set @@ SSet.of_list els_l in
    ps.elts := OMap.add o new_set !(ps.elts)

  let remove_elt_stupid (ps : t') o el =
    remove_elt_stupid' ps o [el]

  let add_map (ps : t) (arr : Cop.AGen.t) (el_s : SGen.t) (el_t : SGen.t) =
    ps.maps := AEMap.add (arr,el_s) el_t !(ps.maps)

  (* this add a map taking into account the chosen datastructure for t' *)
  let add_map' (ps : t') (arr : Cop.AGen.t) (el_s : SGen.t) (el_t : SGen.t) =
    let action = match AEMap.find_opt (arr,el_s) !(ps.maps) with
      | None -> Some [el_t]
      | Some l -> if List.mem el_t l then None else Some (el_t :: l)
    in
    match action with
    | Some new_list ->
      begin
        ps.maps := AEMap.add (arr,el_s) new_list !(ps.maps);
        let inv_new_list = match AEMap.find_opt (arr,el_t) !(ps.inv_maps) with
          | None -> [el_s]
          | Some l -> el_s :: l
        in
        ps.inv_maps := AEMap.add (arr,el_t) inv_new_list !(ps.inv_maps)
      end
    | _ -> ()

  let ctxt_add_map' (ctxt : ctxt) (arr : Cop.AGen.t) (el_s : SGen.t) (el_t : SGen.t) =
    add_map' ctxt.ps arr el_s el_t;
    ctxt_incr_rev ctxt

  (** remove a map from a presheaf, taking care of removing the inverse map. *)
  let remove_map' (ps : t') (arr : Cop.AGen.t) (el_s : SGen.t) (el_t : SGen.t) =
    match AEMap.find_opt (arr,el_s) !(ps.maps) with
    | None -> ()
    | Some l ->
      let (res,new_list) = List.fold_right
          (fun el (res,new_list) ->
             if el = el_t then
               (true,new_list)
             else
               (res,el::new_list)
          )
          l
          (false,[])
      in
      if res then
        begin
          ps.maps := AEMap.add (arr,el_s) new_list !(ps.maps);
          match AEMap.find_opt (arr,el_t) !(ps.maps) with
          | None -> failwith "unexpected case: an invariant on presheaf maps was not preserved."
          | Some l_inv ->
            begin
              let new_l_inv = List.filter ((<>) el_s) l_inv in
              ps.inv_maps := AEMap.add (arr,el_t) new_l_inv !(ps.inv_maps)
            end
        end

  let remove_elt_and_its_maps (ps : t') o el =
    let arrs = Cop.arr_from o in
    List.iter
      (fun arr ->
         let elts = match AEMap.find_opt (arr,el) !(ps.maps) with
           | None -> []
           | Some l -> l
         in
         List.iter
           (fun el_t ->
              remove_map' ps arr el el_t
           )
           elts
      )
      arrs;
    let arrs = Cop.arr_to o in
    List.iter
      (fun arr ->
         let elts = match AEMap.find_opt (arr,el) !(ps.inv_maps) with
           | None -> []
           | Some l -> l
         in
         List.iter
           (fun el_s ->
              remove_map' ps arr el_s el
           )
           elts
      )
      arrs;
    remove_elt_stupid ps o el


  (* let compute_yoneda_obj (o : Cop.OGen.t) =
   *   let gen = SGen.fresh_gen ("y_" ^ (Cop.OGen.to_name o)) in
   *   { elts = ref (OMap.of_seq @@ Seq.return (o, SSet.singleton gen)) ; maps = ref [] } *)

  (* IDENTIFY ELEMENTS AND PRESERVE *-TO-ONE MAPPINGS *)
  (* low-level *)

  (** make several elements equal to one in the presheaf. Also update the
     mappings adequately*)
  (* convention: lhs gets the priority on rhs. *)
  (* *-to-one mapping property might be lost during the process *)
  let equalize_elts' (ps : t') o el1 els_l =
    let new_maps = ref [] in
    let conv = function
      | el when List.mem el els_l -> el1 (* TODO: a Set would be more efficient for mem *)
      | el -> el
    in
    List.iter
      (fun el_to_suppr ->
         let arrs = Cop.arr_from o in
         List.iter
           (fun arr ->
              let els_target = match AEMap.find_opt (arr,el_to_suppr) !(ps.maps) with
                | None -> []
                | Some l -> l
              in
              List.iter
                (fun el_target ->
                   Utils.tell new_maps (o,arr,el1,conv el_target)
                )
                els_target
           )
           arrs;
         let arrs = Cop.arr_to o in
         List.iter
           (fun arr ->
              let els_source = match AEMap.find_opt (arr,el_to_suppr) !(ps.inv_maps) with
                | None -> []
                | Some l -> l
              in
              let o_source = Cop.src arr in
              List.iter
                (fun el_source ->
                   Utils.tell new_maps (o_source,arr,conv el_source,el1)
                )
                els_source
           )
           arrs;
         remove_elt_and_its_maps ps o el_to_suppr
      )
      els_l;
    List.iter
      (fun (o,arr,el_s,el_t) ->
         add_map' ps arr el_s el_t
      )
      !new_maps

  let ctxt_equalize_elts' ctxt o el1 els_l =
    let el1 = ctxt_get_rep ctxt o el1 in
    let els_l = List.map (ctxt_get_rep ctxt o) els_l in
    let els_l = List.filter ((<>) el1) els_l in
    if List.compare_length_with els_l 0 > 0 then
      ctxt_incr_rev ctxt ;
    let ps = ctxt_get_ps ctxt in
    equalize_elts' ps o el1 els_l;
    List.iter
      (fun el_suppr ->
         ctxt_set_new_rep ctxt o el_suppr el1
      )
      els_l

  (** equalize one pair of elements *)
  (* *-to-one mapping property might be lost during the process *)
  let equalize_elts (ps : t') o el1 el2 =
    equalize_elts' ps o el1 [el2]

  let ctxt_equalize_elts ctxt o el1 el2 =
    ctxt_equalize_elts' ctxt o el1 [el2]

  (** find parallel mappings in a presheaf. *)
  (* typically called after a function like equalize_elts which might create new mappings. *)
  (* one should call equalize_elts on the resulting mappings in order to get a *-to-1 presheaf. *)
  let find_parallel_maps (ps : t') =
    let res = ref [] in
    ps_foreach_oelt ps
      (fun (o,el) ->
         let arrs = Cop.arr_from o in
         List.iter
           (fun arr ->
              match AEMap.find_opt (arr,el) !(ps.maps) with
              | Some l when List.compare_length_with l 1 > 0 -> Utils.tell res ((el,arr),l)
              | _ -> ()
           )
           arrs
      );
    !res

  let ctxt_find_parallel_maps ctxt =
    find_parallel_maps ctxt.ps

  (** enforce an equality in the presheaf between two elements (of the same type) *)
  (* the first element is the one which stays *)
  let rec enforce_many_to_one (ps : t') =
    let pmaps = find_parallel_maps ps in
    match pmaps with
    | [] -> false
    | ((el,arr),els_l) :: q ->
      begin
        match els_l with
        | el1 :: q when List.length q > 0 ->
          equalize_elts' ps (Cop.tgt arr) el1 q;
          ignore @@ enforce_many_to_one ps;
          true
        (* when several elements are equalized, the other elements of pmaps are
           not up-to-date and are then recomputed using a recursive call. *)
        (* TODO: make something more efficient here ^.*)
        | _ -> failwith "An encountered case was not supposed to happen."
      end

  let rec ctxt_enforce_many_to_one (ctxt : ctxt) =
    let pmaps = ctxt_find_parallel_maps ctxt in
    List.iter
      (fun ((el,arr),els_l) ->
         match els_l with
         | el1 :: q when List.compare_length_with q 0 > 0 ->
           ctxt_equalize_elts' ctxt (Cop.tgt arr) el1 q
         | _ -> failwith "An encountered case was not supposed to happen."
      )
      pmaps

  (** compute the pairs of elements that must be equalized w.r.t an equation. *)
  let compute_equation_pairs ps (p1,p2) =
    let o = Cop.psrc p1 in
    let elts = match OMap.find_opt o !(ps.elts) with
      | None -> SSet.empty
      | Some s -> s
    in
    let res = ref [] in
    SSet.iter
      (fun el ->
         let oel1 = path_to_map_opt' ps p1 el in
         let oel2 = path_to_map_opt' ps p2 el in
         let otgt = Cop.ptgt p1 in
         match (oel1,oel2) with
         | (Some el1,Some el2) when el1 <> el2 -> res := (otgt,el1,el2) :: !res
         | _ -> ()
      )
      elts;
    Utils.list_remove_duplicate compare !res

  let ctxt_compute_equation_pairs ctxt (p1,p2) =
    compute_equation_pairs ctxt.ps (p1,p2)

  let compute_equations_pairs ps l =
    let res = List.concat @@ List.map (compute_equation_pairs ps) l in
    Utils.list_remove_duplicate compare res

  let ctxt_compute_equations_pairs ctxt l =
    compute_equations_pairs ctxt.ps l

  let enforce_equations_one_step (ps : t') =
    let eqs = Cop.equations in
    let res = compute_equations_pairs ps eqs in
    let rec aux = function
      | [] -> false
      | (o,l,r) :: q when l <> r ->
        equalize_elts ps o l r;
        (* here we use the fact that equalize_elts preserves the first element and not the second *)
        let conv = function
          | x when x = r -> l
          | x -> x
        in
        let conv' = fun (o',l',r') -> (o',conv l',conv r') in
        ignore (aux (List.map conv' q)); true
      | _ :: q -> aux q
    in
    aux res

  (** expand a partial definition of a morphism between two expanded presheaves psA and psB. *)
  (* TODO: make this return unit *)
  let morph_expand psA (* expanded *) psB (* expanded *) (m : morph) =
    let curr_domain = ref SSet.empty in
    let start = !m in
    m := [];
    let rec aux = function
      | [] -> m
      | (o,s,t) :: q when SSet.mem s !curr_domain -> aux q
      | (o,s,t) :: q ->
        begin
          curr_domain := SSet.add s !curr_domain;
          morph_add m o s t;
          let arrs = Cop.arr_from o in
          let to_add = List.map
              (fun arr ->
                 let new_o = Cop.tgt arr in
                 let (_,_,new_s) = arr_to_map' psA arr s in
                 let (_,_,new_t) = arr_to_map' psB arr t in
                 (new_o,new_s,new_t)
              )
              arrs
          in
          aux @@ to_add @ q
        end
    in
    aux start

  let ctxt_enforce_equations_one_step (ctxt : ctxt) =
    let eqs = Cop.equations in
    let res = ctxt_compute_equations_pairs ctxt eqs in
    List.iter
      (fun (o,l,r) ->
         ctxt_equalize_elts ctxt o l r
      )
      res

  (** close the presheaf by the operations and the equations of the presented category. *)
  (** do not progressively unify the new elements with equalities so that it can diverge easily. *)
  let expand_presheaf_stupid (ps : t) =
    (* let start_nodes = OMap.bindings !(ps.elts) in *)
    let rec aux curr_nodes =
      let built_nodes = ref [] in
      List.iter (fun (o,el) ->
        let arrs = Cop.arr_from o in
        (* we iterate to build elements for mappings that do not already exist *)
        List.iter (fun arr -> 
            let target_o = Cop.tgt arr in
            match arr_to_map_opt ps arr el with
            | Some _ -> ()
            | None -> begin
                let target_el = SGen.fresh_gen (SGen.to_name el ^ ";" ^ Cop.AGen.to_name arr) in
                add_el ps target_o target_el;
                add_map ps arr el target_el;
                built_nodes := (target_o,target_el) :: !built_nodes
                (** TODO: should we keep track of new mappings with a built_mappings? *)
              end
          ) arrs
        ) curr_nodes;
      (* TODO: merge elements here *)
      (* call a function like "apply_equalities" *)
      match !built_nodes with
      | [] -> ()
      | s  -> aux s
    in (ignore @@ aux [] ; failwith "function not complete.")
       (* the above aux [] is just to remove a warning. do not mind it. *)

  let expand_presheaf_naive (ps : t) =
    let bindings = OMap.bindings !(ps.elts) in
    let start_nodes = List.concat @@ List.map
        (fun (o,s) ->
           List.map (fun el -> (o,el)) @@ Utils.seq_to_list @@ SSet.to_seq s
        )
        bindings
    in
    let rec aux curr_nodes =
      let built_nodes = ref [] in
      List.iter (fun (o,el) ->
        let arrs = Cop.arr_from o in
        (* we iterate to build elements for mappings that do not already exist *)
        List.iter (fun arr -> 
            let target_o = Cop.tgt arr in
            match arr_to_map_opt ps arr el with
            | Some _ -> ()
            | None -> begin
                let target_el = SGen.fresh_gen (SGen.to_name el ^ ";" ^ Cop.AGen.to_name arr) in
                add_el ps target_o target_el;
                add_map ps arr el target_el;
                built_nodes := (target_o,target_el) :: !built_nodes
                (** TODO: should we keep track of new mappings with a built_mappings? *)
              end
          ) arrs
        ) curr_nodes;
      (* TODO: merge elements here *)
      (* call a function like "apply_equalities" *)
      match !built_nodes with
      | [] -> ()
      | s  -> aux s
    in aux start_nodes

  (** build missing elements for current elements and arrow generators. *)
  (* note: it preserves the *-to-1 property. *)
  let expand_presheaf_one_step (ps : t') =
    let bindings = OMap.bindings !(ps.elts) in
    let start_nodes = List.concat @@ List.map
        (fun (o,s) ->
           List.map (fun el -> (o,el)) @@ Utils.seq_to_list @@ SSet.to_seq s
        )
        bindings
    in
    let amap = raw_to_assoc_mappings !(ps.maps) in
    let built_nodes = ref [] in
    List.iter (fun (o,el) ->
      let arrs = Cop.arr_from o in
      (* we iterate to build elements for mappings that do not already exist *)
      List.iter (fun arr -> 
          let target_o = Cop.tgt arr in
          match assoc_arr_to_map_opt amap arr el with
          | Some _ -> ()
          | None -> begin
              let target_el = SGen.fresh_gen (SGen.to_name el ^ ";" ^ Cop.AGen.to_name arr) in
              add_el' ps target_o target_el;
              add_map' ps arr el target_el;
              built_nodes := (target_o,target_el) :: !built_nodes
              (** TODO: should we keep track of new mappings with a built_mappings? *)
            end
        ) arrs
      ) start_nodes;
    !built_nodes

  (* ctxt version of expand_presheaf_one_step *)
  let ctxt_expand_presheaf_one_step (ctxt : ctxt) =
    let amap = raw_to_assoc_mappings !(ctxt.ps.maps) in
    ps_foreach_oelt ctxt.ps
      (fun (o,el) ->
      let arrs = Cop.arr_from o in
      (* we iterate to build elements for mappings that do not already exist *)
      List.iter (fun arr -> 
          let target_o = Cop.tgt arr in
          match assoc_arr_to_map_opt amap arr el with
          | Some _ -> ()
          | None -> begin
              let target_el = SGen.fresh_gen (SGen.to_name el ^ ";" ^ Cop.AGen.to_name arr) in
              ctxt_add_el' ctxt target_o target_el;
              ctxt_add_map' ctxt arr el target_el
              (** TODO: should we keep track of new mappings with a built_mappings? *)
            end
        ) arrs)

  (* generate a correct presheaf w.r.t the *-to-1 property and the equations of the category. *)
  let rec expand_presheaf_interleaved (ps : t') =
    let res1 = expand_presheaf_one_step ps in
    let res2 = enforce_equations_one_step ps in
    let res3 = enforce_many_to_one ps in
    if (res1 <> [] || res2 || res3 ) then
      (ignore @@ expand_presheaf_interleaved ps ; true)
    else
      false

  let rec ctxt_presheaf_interleaved (ctxt : ctxt) =
    let old_rev = ctxt_get_rev ctxt in
    ctxt_expand_presheaf_one_step ctxt ;
    ctxt_enforce_equations_one_step ctxt ;
    ctxt_enforce_many_to_one ctxt ;
    let new_rev = ctxt_get_rev ctxt in
    if old_rev < new_rev then
      ctxt_presheaf_interleaved ctxt
    else
      ()


  (** check the existing commutativity conditions on a presheaf morphism. *)
  (* the target ps must be sufficiently expanded (to be precised). *)
  (* *-to-1 is assumed for m. *)
  let check_morph' (psA : t') (psB : t') (m : (Cop.OGen.t * SGen.t * SGen.t) list) =
    try
      let mapA = raw_to_assoc_mappings !(psA.maps) in
      let mapB = raw_to_assoc_mappings !(psB.maps) in
      let aassoc = List.map (fun o -> (o,Cop.arr_from o)) Cop.objects in
      let oamap = OMap.of_seq @@ Utils.list_to_seq aassoc in
      List.iter
        (fun (o,el_s,el_t) ->
           let arrows = match OMap.find_opt o oamap with
             | None -> []
             | Some l -> l
           in
           List.iter
             (fun arr ->
                let im11 = AEMap.find_opt (arr,el_s) mapA in
                let im12 = Option.bind
                    im11
                    (fun el ->
                       let res = List.find_opt
                                   (fun (o,s,t) -> s = el)
                                   m
                       in
                       Option.bind res (fun (o,s,t) -> Some t)
                    )
                in
                match im12 with
                | None -> ()
                | Some el1 ->
                  begin
                    let im2 = AEMap.find_opt (arr,el_t) mapB in
                    match im2 with
                    | None -> raise Stdlib.Exit
                    | Some el2 ->
                      begin
                        if el1 <> el2 then
                          raise Stdlib.Exit;
                        ()
                      end
                  end
             )
             arrows
        )
        m;
      true
    with
    | _ -> false

  (* compute an association list whose elements are (b,[a1,...,an]) where ai is
     a preimage of b by f *)
  let compute_inv_maps psA psB (mf : morph) =
    let module OEMap = Map.Make(struct
        type t = Cop.obj_t * SGen.t
        let compare = compare
      end) in
    let res = ref OEMap.empty in
    List.iter
      (fun (o,el_s,el_t) ->
         res := OEMap.update
           (o,el_t)
           (function
             | None -> Some [el_s]
             | Some u -> Some (el_s :: u)
           )
           !res
      )
      !mf;
    OEMap.bindings !res

  (* compute the liftings of g : A -> X along f : A -> B *)
  let compute_ps_liftings (psA : t') (psB : t') (mf : morph) (psX : t') (mg : morph) =
    fpf "compute_ps_liftings@.";
    let oelts = compute_oelt_pairs psB in
    let oelts = List.sort (fun (_,l) (_,r) -> compare_with_priority l r) oelts in
    fpf "list of oelt pairs:@.[";
    List.iter (fun (o,elt) ->
        fpf "(%s,%s)," (Cop.obj_to_name o) (SGen.to_name elt)
    ) oelts;
    fpf "]@.";
    let invmap = compute_inv_maps psA psB mf in
    let res = ref [] in
    let rec explore next_oelts sol = match next_oelts with
      | [] -> res := (ref sol) :: !res
      | oelt :: next_oelts ->
        begin
          let (o,b) = oelt in
          let invb = match Utils.list_find_opt (fun ((_,b'),l') -> b = b') invmap with
            | None -> []
            | Some (b',l') -> l'
          in
          let possible_images = match invb with
            | [] -> (match OMap.find_opt o !(psX.elts) with
                | None -> []
                | Some s -> Utils.seq_to_list @@ SSet.to_seq s)
            | a :: q ->
              let x = morph_img mg a in
              if List.for_all (fun a' -> morph_img mg a' = x) q then
                [x]
              else
                []
          in
          List.iter
            (fun x ->
               let sol' = (o,b,x) :: sol in
               if check_morph' psB psX sol' then
                 explore next_oelts sol'
            )
            possible_images
        end
    in
    explore oelts [];
    !res

  (** same as enforce_many_to_one but compute a projection. *)
  (* the first element is the one which stays *)
  (* TODO: finish this. *)
  (* let rec enforce_many_to_one_proj (ps : t') (proj : morph) =
   *   let pmaps = find_parallel_maps ps in
   *   match pmaps with
   *   | [] -> false
   *   | ((el,arr),els_l) :: q ->
   *     begin
   *       match els_l with
   *       | el1 :: q when List.length q > 0 ->
   *         equalize_elts' ps (Cop.tgt arr) el1 q;
   *         ignore @@ enforce_many_to_one_proj ps proj;
   *         true
   *       (\* when several elements are equalized, the other elements of pmaps are
   *          not up-to-date and are then recomputed using a recursive call. *\)
   *       (\* TODO: make something more efficient here ^.*\)
   *       | _ -> failwith "An encountered case was not supposed to happen."
   *     end *)


  (** compute the morphisms g : A -> X **)
  let compute_ps_morphs psA psX =
    let psEmpty = ps_empty' () in
    let mEmpty1 = morph_empty () in
    let mEmpty2 = morph_empty () in (* TODO: incoherent naming between ps_empty' and morph_empty *)
    compute_ps_liftings psEmpty psA mEmpty1 psX mEmpty2

  (** construct a copy of a presheaf and rename its elements. *)
  (* returns the copy B' of B with a morphism B -> B'. *)
  let ps_make_renamed_copy psB rename_fun =
    let psB' = ps_empty' () in
    let oelts = !(psB.elts) in
    let mBB' = morph_empty () in
    OMap.iter
      (fun o s ->
         SSet.iter
           (fun el ->
              let new_el = SGen.fresh_gen (rename_fun o el) in
              add_el' psB' o new_el;
              morph_add mBB' o el new_el
           )
           s
      )
      oelts;
    ps_foreach_map
      psB
      (fun (el_s,arr,el_t) ->
         add_map' psB' arr (morph_img mBB' el_s) (morph_img mBB' el_t)
      );
    (psB',mBB')

  let ps_make_copy psB =
    ps_make_renamed_copy psB (fun o el -> SGen.to_name el)

  let morph_comp l r =
    let res = List.map
        (fun (o,el_s,el_t) ->
           let middle = morph_img l el_s in
           (o,el_s,morph_img r middle)
        )
        !l
    in
    ref res
  (** compose two morphisms l and r where r is partially defined. *)
  (* the non-defined mappings in r are assumed to be identities. *)
  let morph_comp_with_partial_r l r =
    let res = List.map
        (fun (o,el_s,el_t) ->
           let middle = morph_img l el_s in
           match morph_img_opt r o middle with
           | None -> (o,el_s,middle)
           | Some u -> (o,el_s,u)
        )
        !l
    in
    ref res

  (* WARNING: no copy made for the ctxt version. *)
  let ctxt_add_unify_construction ctxt new_elts new_maps new_equalities =
    List.iter
      (fun (o,new_el) ->
         ctxt_add_el' ctxt o new_el
      )
      new_elts;
    List.iter
      (fun (arr,el_s,el_t) ->
         ctxt_add_map' ctxt arr el_s el_t
      )
      new_maps;
    List.iter (fun (o,l,r) -> ctxt_equalize_elts ctxt o l r) new_equalities

  (* add a copy of a presheaf. *)
  let ctxt_add_ps_copy (ctxt : ctxt) (ps : t') : morph =
    let new_elts = ref [] in
    let new_maps = ref [] in
    let (psCopy,m) = ps_make_copy ps in
    (*TODO: better names for the copy. *)
    ps_foreach_oelt psCopy (fun (o,el) ->
        Utils.tell new_elts (o,el)
      ) ;
    ps_foreach_map psCopy (fun (el_s,arr,el_t) ->
        Utils.tell new_maps (arr,el_s,el_t)
      ) ;
    ctxt_add_unify_construction ctxt !new_elts !new_maps [] ;
    m

  let ctxt_enforce_ex_lifting_step ortho_maps (ctxt : ctxt) =
    let new_elts = ref [] in
    let new_maps = ref [] in
    let new_equations = ref [] in
    let tell_new_elt (o,elt) =
      new_elts := (o,elt) :: !new_elts
    in
    let tell_new_map (arr,el_s,el_t) =
      new_maps := (arr,el_s,el_t) :: !new_maps
    in
    let tell_new_equation (o,el1,el2) =
      new_equations := (o,el1,el2) :: !new_equations
    in
    List.iteri
      (fun i (psA,psB,mF) ->
         fpf "ortho map n°%d@." i;
         let mAtoX_l = compute_ps_morphs psA ctxt.ps in
         match morph_is_epi psA psB mF with
         | true ->
           begin
             List.iter
               (fun mAtoX ->
                  let invmap = compute_inv_maps psA psB mF in
                  List.iter
                    (fun ((o,elB),elA_l) ->
                       let firstAr = ref None in
                       List.iter
                         (fun elA ->
                            match !firstAr with
                            | None -> firstAr := Some elA
                            | Some firstA -> tell_new_equation (o,morph_img mAtoX firstA,morph_img mAtoX elA)
                         )
                         elA_l
                    )
                    invmap)
               mAtoX_l
           end
         | false ->
             begin
               let morphs_and_liftings = List.map
                   (fun mAtoX ->
                      let liftings = compute_ps_liftings psA psB mF ctxt.ps mAtoX in
                      (mAtoX,liftings)
                   )
                   mAtoX_l
               in
               fpf "morph and liftings computed. Total: %d@." (List.length morphs_and_liftings);
               let morphs_no_lifting = List.filter_map
                   (function
                     | (f,[]) -> Some f
                     | _ -> None)
                   morphs_and_liftings
               in
               List.iter
                 (fun mG ->
                    fpf "morph computed@.";
                    let rename_fun o el = "lift("^ SGen.to_name el ^"_" ^ string_of_int (fresh ()) ^ ")" in
                    let (psB',mBB') = ps_make_renamed_copy psB rename_fun in
                    ps_foreach_oelt psB' tell_new_elt;
                    ps_foreach_map psB' (fun (el_s,arr,el_t) -> tell_new_map (arr,el_s,el_t));
                    ps_foreach_oelt psA (fun (o,elA) ->
                        let elB = morph_img mF elA in
                        let elB' = morph_img mBB' elB in
                        let elX = morph_img mG elA in
                        tell_new_equation (o,elX,elB')
                      )
                 )
                 morphs_no_lifting
             end
      )
      ortho_maps;
    ctxt_add_unify_construction ctxt !new_elts !new_maps !new_equations

  let ctxt_enforce_unique_lifting_step ortho_maps (ctxt : ctxt) =
    let new_equations = ref [] in
    let tell_new_equation (o,el1,el2) =
      new_equations := (o,el1,el2) :: !new_equations
    in
    List.iteri
      (fun i (psA,psB,mF) ->
         match morph_is_epi psA psB mF with
         | true -> (fpf "m %d is epi@." i)
         | false ->
           begin
             (* Format.printf "orthogonal morph %d@." i; *)
             let mAtoX_l = compute_ps_morphs psA ctxt.ps in
             let morphs_and_liftings = List.map
                 (fun mAtoX ->
                    (* Format.printf "morph found:@.";
                     * print_morph mAtoX; *)
                    let liftings = compute_ps_liftings psA psB mF ctxt.ps mAtoX in
                    (mAtoX,liftings)
                 )
                 mAtoX_l
             in
             let morphs_many_liftings = List.filter_map
                 (function
                   | (f,l) when List.compare_length_with l 1 > 0 -> Some (f,l)
                   | _ -> None)
                 morphs_and_liftings
             in
             List.iter
               (fun (mG,mG'_l) ->
                  ps_foreach_oelt psB
                    (fun (o,elB) ->
                       let imgs = List.map
                           (fun mG' ->
                              morph_img mG' elB
                           )
                           mG'_l
                       in
                       match imgs with
                       | [] -> failwith "Unexpected case encountered."
                       | first_elX :: q ->
                         List.iter
                           (fun elX ->
                              tell_new_equation (o,first_elX,elX)
                           )
                           q
                    )
               )
               morphs_many_liftings
           end
      )
      ortho_maps ;
    ctxt_add_unify_construction ctxt [] [] !new_equations

  (* TODO: finish this function. *)
  (* let compute_ortho ortho_maps psX =
   *   let curr_ps = failwith "code idX" in
   *   let curr_proj = failwith "code idX" in
   *   let b1 = expand_presheaf_interleaved curr_ps in
   *   let (psX',mXX') = enforce_ex_lifting_step ortho_maps psX in
   *   curr_ps := psX';
   *   curr_proj := morph_comp_with_partial_r curr_proj mXX';
   *   let b3 := ref false and continue = ref true in
   *   while !continue do
   *     let (b,psX'',mX'X'') = enforce_unique_lifting_step ortho_maps psX in
   *     curr_proj := morph_comp_with_partial_r curr_proj mX'X'';
   *     let b1 = expand_presheaf_interleaved curr_ps in
   *     if b = false then
   *       continue := false
   *     else
   *       b3 := true;
   *   done; *)

  let rec ctxt_compute_ortho ortho_maps (ctxt : ctxt) =
    let old_rev = ctxt_get_rev ctxt in
    fpf "entering@.";
    ctxt_presheaf_interleaved ctxt ;
    fpf "after interleaved@.";
    ctxt_enforce_unique_lifting_step ortho_maps ctxt;
    ctxt_enforce_ex_lifting_step ortho_maps ctxt ;
    fpf "after ex lifting:@.";
    print_ps_elts' @@ ctxt_get_ps ctxt;
    ctxt_presheaf_interleaved ctxt ;
    fpf "@.";
    let r_rev = ref (-1) in
    while (!r_rev < ctxt_get_rev ctxt) do
      fpf "starting a loop@.";
      r_rev := ctxt_get_rev ctxt ;
      ctxt_enforce_unique_lifting_step ortho_maps ctxt;
      ctxt_presheaf_interleaved ctxt ;
      fpf "after a loop:@.";
      print_ps_elts' @@ ctxt_get_ps ctxt;
      fpf "@.";
    done ;
    if (old_rev < ctxt_get_rev ctxt) then
      ctxt_compute_ortho ortho_maps ctxt
    else
      (fpf "leaving@.")

  (** compute the reflection of a map. ctxtX and ctxtY must be already orthogonalized. *)
  let ctxt_compute_ortho_map ortho_maps (ctxtX : ctxt) (ctxtY : ctxt) (m : morph) =
    let psXo = ctxtX.ps and psYo = ctxtY.ps in
    let mo = morph_empty () in
    let curr_domain = ref SSet.empty in
    List.iter
      (fun (o,s) ->
         SSet.iter
           (fun el ->
              let el_s = ctxt_get_rep ctxtX o el in
              let el_mid = morph_img m el in
              let el_t = ctxt_get_rep ctxtY o el_mid in
              if not @@ SSet.mem el_s !curr_domain then
                (
                  morph_add mo o el_s el_t;
                  curr_domain := SSet.add el_s !curr_domain
                )
           )
           s
      )
      @@ OMap.bindings ctxtX.init_elts ;
      let xo_liftings = List.concat @@ List.map
          (fun ((psA,psB,mF) as omap) ->
             let mAtoX_l = compute_ps_morphs psA psXo in
             List.map
               (fun mAtoX ->
                  let liftings = compute_ps_liftings psA psB mF psXo mAtoX in
                  match liftings with
                  | [lift] ->
                    let cod = morph_codomain mAtoX in
                    (omap,mAtoX,lift,cod)
                  | _ -> failwith "Unexpected case encountered."
               )
               mAtoX_l
          )
          ortho_maps
      in
      let rec aux curr_l next_l = match (curr_l,next_l) with
        | ([],[]) -> ()
        | ([],q) -> aux (List.rev q) []
        | (((omap,mAtoX,mBtoX,cod) as curr) :: q1 , q2) ->
          begin
            if SSet.is_empty (SSet.diff cod !curr_domain) then
              let mAtoY = morph_comp mAtoX mo in
              let (psA,psB,mF) = omap in
              let mBtoYs = compute_ps_liftings psA psB mF psYo mAtoY in
              begin
              match mBtoYs with
              | [mBtoY] ->
                ps_foreach_oelt psB
                  (fun (o,el) ->
                     let elX = morph_img mBtoX el in
                     if SSet.mem elX !curr_domain then
                       ()
                     else
                       (let elY = morph_img mBtoY el in
                        morph_add mo o elX elY ;
                        curr_domain := SSet.add elX !curr_domain)
                  ) ;

              | _ -> failwith "Unexpected case encountered."
              end ;
                aux q1 q2
            else
              aux q1 (curr :: q2)
          end
      in
      aux xo_liftings [] ;
      (* TODO: this should not be necessary: *)
      morph_normalize mo ;
      mo

  (* Product construction *)
  type prod_res = { ps : t' ; emb : Cop.OGen.t -> SGen.t -> SGen.t -> SGen.t }

  let prod_res_get_ps (pres : prod_res) = pres.ps

  (** build the product of two presheaves. **)
  (* NOTE: both input presheaves are assumed fully expanded *)
  let compute_prod psA (* fully expanded *) psB (* fully expanded *) =
    let psRes = ps_empty' () in
    let new_elts = ref [] in
    ps_foreach_oelt psA (fun (oA,elA) ->
        let sB = elts_of_type psB oA in
        SSet.iter (fun elB ->
            let new_el = SGen.fresh_gen @@ "(" ^ SGen.to_name elA ^ "," ^ SGen.to_name elB ^ ")" in
            add_el' psRes oA new_el;
            Utils.tell new_elts (oA,elA,elB,new_el)
          )
          sB
      );
    let module OEEMap = Map.Make (struct
        type t = Cop.OGen.t * SGen.t * SGen.t
        let compare = compare
      end) in
    let emb_map = ref OEEMap.empty in
    List.iter (fun (o,elA,elB,new_el) ->
        emb_map := OEEMap.add (o,elA,elB) new_el !emb_map
      )
      !new_elts;
    ps_foreach_map psA (fun (el_s_A,arrA,el_t_A) ->
        ps_foreach_map psB (fun (el_s_B,arrB,el_t_B) ->
            (* TODO: be more optimal than ps_foreach_map on A and B*)
            if arrA = arrB then
              begin
                let os = Cop.src arrA in
                let ot = Cop.tgt arrA in
                let new_el_s = OEEMap.find (os,el_s_A,el_s_B) !emb_map in
                let new_el_t = OEEMap.find (ot,el_t_A,el_t_B) !emb_map in
                add_map' psRes arrA new_el_s new_el_t
              end
          )
      );
    { ps = psRes ; emb = fun o elA elB -> OEEMap.find (o,elA,elB) !emb_map }

  let compute_prod_map_r psX psA psB mAB prodXA prodXB =
    let mRes = morph_empty () in
    ps_foreach_oelt psA (fun (oA,elA) ->
        let sX = elts_of_type psX oA in
        SSet.iter (fun elX ->
            let elB = morph_img mAB elA in
            morph_add mRes oA (prodXA.emb oA elX elA) (prodXB.emb oA elX elB)
          )
          sX
      ) ;
    mRes
end

module type TheoryT = sig
  module Cat : Category
  module Ps : PresheafT with module C = Cat
  val ortho_maps : (Ps.t' * Ps.t' * Ps.morph) list
end

module type FunctorPresT = sig
  module SourceTheory : TheoryT
  module TargetTheory : TheoryT
  type t = {
      obj_map : SourceTheory.Cat.obj_t -> TargetTheory.Ps.t' ;
      map_map : SourceTheory.Cat.arr_t -> TargetTheory.Ps.morph
    }
  type obj_map_res = {
    ps : TargetTheory.Ps.t';
    proj : (SourceTheory.Cat.obj_t * SourceTheory.Ps.SGen.t) -> TargetTheory.Ps.morph
  }
  val ps_obj_map : t -> SourceTheory.Ps.t' -> obj_map_res
  val ps_map_map : t -> SourceTheory.Ps.t' -> SourceTheory.Ps.t' -> SourceTheory.Ps.morph -> obj_map_res -> obj_map_res -> TargetTheory.Ps.morph
  val is_left_adjoint : t -> bool
end

module FunctorPres (S : TheoryT) (T : TheoryT) (* : FunctorPresT *) = struct
  (* uncomment ^ when the code is finalized. *)
  module SourceTheory = S
  module TargetTheory = T

  type t = {
      obj_map : SourceTheory.Cat.obj_t -> TargetTheory.Ps.t' ;
      map_map : SourceTheory.Cat.arr_t -> TargetTheory.Ps.morph
    }

  type obj_map_res = {
    ps : TargetTheory.Ps.t';
    proj : (SourceTheory.Cat.obj_t * SourceTheory.Ps.SGen.t) -> TargetTheory.Ps.morph
  }

  let ps_obj_map presFunct psS =
    let ctxtRes = T.Ps.create_ctxt (T.Ps.ps_empty' ()) in
    let module OEMap = Map.Make (struct
        type t = (S.Cat.obj_t * S.Ps.SGen.t)
        let compare = compare
      end) in
    let proj_per_el = ref OEMap.empty in
    (* ^ projections in the copy of the presheaves induced by the elements of psS. *)
    S.Ps.ps_foreach_oelt psS (fun (o,el) ->
        let m = T.Ps.ctxt_add_ps_copy ctxtRes (presFunct.obj_map o) in
        proj_per_el := OEMap.add (o,el) m !proj_per_el
    ) ;
    let new_equalities = ref [] in
    S.Ps.ps_foreach_map psS (fun (el_s_S,arr,el_t_S) ->
        let m_T = presFunct.map_map arr in
        let o_S_ps_s_T = S.Cat.src arr in
        let o_S_ps_t_T = S.Cat.tgt arr in
        let ps_s_T = presFunct.obj_map o_S_ps_s_T in
        (* let ps_t_T = presFunct.obj_map o_S_ps_t_T in *)
        let proj_ps_s_T = OEMap.find (o_S_ps_s_T,el_t_S) !proj_per_el in
        let proj_ps_t_T = OEMap.find (o_S_ps_t_T,el_s_S) !proj_per_el in
        T.Ps.ps_foreach_oelt ps_s_T
          (fun (o_T,el_T) ->
             let rep_s = T.Ps.morph_img proj_ps_s_T el_T in
             let mid = T.Ps.morph_img m_T el_T in
             let rep_t = T.Ps.morph_img proj_ps_t_T mid in
             Utils.tell new_equalities (o_T,rep_s,rep_t)
          )
      ) ;
    T.Ps.ctxt_add_unify_construction ctxtRes [] [] !new_equalities ;
    let new_proj_per_el = OEMap.map
          (fun (m : T.Ps.morph) ->
             T.Ps.morph_from_map @@ List.map (fun (o,el_s,el_t) ->
                 (o,el_s,T.Ps.ctxt_get_rep ctxtRes o el_t)
               ) @@ T.Ps.morph_to_map m
                (* TODO: introduce a function morph_from_map and remove ref @@ here *)
          )
          !proj_per_el
    in
    {
      ps = T.Ps.ctxt_get_ps ctxtRes;
      proj = fun (o,el) -> OEMap.find (o,el) new_proj_per_el
    }

  let ps_map_map presFunct psA psB mF (imgA : obj_map_res) (imgB : obj_map_res) =
    let mRes = T.Ps.morph_empty () in
    let module SSet = Set.Make(T.Ps.SGen) in
    let dom = ref SSet.empty in
    let dom_tell el = dom := SSet.add el !dom in
    let dom_already_here el = SSet.mem el !dom in
    S.Ps.ps_foreach_oelt psA (fun (o_S,elA) ->
        let ps_T = presFunct.obj_map o_S in
        let m_ps_T_to_imA = imgA.proj (o_S,elA) in
        let elB = S.Ps.morph_img mF elA in
        let m_ps_T_to_imB = imgB.proj (o_S,elB) in
        T.Ps.ps_foreach_oelt ps_T (fun (o_T,el_T) ->
            let el_imA_T = T.Ps.morph_img m_ps_T_to_imA el_T in
            if not @@ dom_already_here el_imA_T then
              begin
                let el_imB_T = T.Ps.morph_img m_ps_T_to_imB el_T in
                T.Ps.morph_add mRes o_T el_imA_T el_imB_T ;
                dom_tell el_imA_T
              end
          )
      ) ;
    mRes

  let is_left_adjoint presFunct =
    try
      List.iteri (fun i ortho_map ->
          let (psA,psB,mF) = ortho_map in
          let imA_infos = ps_obj_map presFunct psA in
          let imB_infos = ps_obj_map presFunct psB in
          let im_mF = ps_map_map presFunct psA psB mF imA_infos imB_infos in
          let ctxt_imA = T.Ps.create_ctxt imA_infos.ps in
          let ctxt_imB = T.Ps.create_ctxt imB_infos.ps in
          T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imA;
          T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imB;
          let im_mF_ortho = T.Ps.ctxt_compute_ortho_map TargetTheory.ortho_maps ctxt_imA ctxt_imB im_mF in
          Format.printf "@[<v 0>Test n°%d for left adjointness:@,@[<v 2>@," (i+1);
          Format.printf "Orthogonalized source:@,";
          T.Ps.print_ps_elts' (T.Ps.ctxt_get_ps ctxt_imA);
          Format.printf "Orthogonalized target:@,";
          T.Ps.print_ps_elts' (T.Ps.ctxt_get_ps ctxt_imB);
          Format.printf "Reflected map between them:@,";
          T.Ps.print_morph (im_mF_ortho);
          Format.printf "@]@,@]@.";
          if not @@ T.Ps.morph_is_iso (T.Ps.ctxt_get_ps ctxt_imA) (T.Ps.ctxt_get_ps ctxt_imB) im_mF_ortho then
            begin
              Format.printf "The orthogonalization map %d is not sent to an isomorphism.@." (i+1);
              raise Exit
            end
        )
        SourceTheory.ortho_maps ;
      true
    with
    | Exit -> false
end
