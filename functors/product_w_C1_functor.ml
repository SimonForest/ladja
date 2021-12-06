module FP = Lib2.FunctorPres(CategoryCat)(CategoryCat)

module PsC = FP.SourceTheory.Ps

module OMap = Map.Make (struct
    type t = CategoryCat.Cat.obj_t
    let compare = compare
  end)

module AMap = Map.Make (struct
    type t = CategoryCat.Cat.arr_t
    let compare = compare
  end)

let yoneda_ps =
  let res = ref OMap.empty in
  List.iter (fun o ->
      let ps = PsC.ps_empty' () in
      let y_el = PsC.SGen.fresh_gen @@ "y(" ^ CategoryCat.Cat.obj_to_name o ^ ")" in
      PsC.add_el' ps o y_el;
      let ctxt = PsC.create_ctxt ps in
      PsC.ctxt_presheaf_interleaved ctxt;
      let y_el = PsC.ctxt_get_rep ctxt o y_el in
      res := OMap.add o (PsC.ctxt_get_ps ctxt,y_el) !res
    )
    CategoryCat.Cat.objects;
  !res

let yoneda_maps =
  let res = ref AMap.empty in
  List.iter (fun arr ->
      let m = PsC.morph_empty () in
      let o_src = CategoryCat.Cat.src arr in
      let o_tgt = CategoryCat.Cat.tgt arr in
      let (yps_S,yel_S) = OMap.find o_src yoneda_ps in
      let (yps_T,yel_T) = OMap.find o_tgt yoneda_ps in
      let el_T_t = PsC.arr_to_map' yps_T arr yel_T in
      PsC.morph_add m o_src yel_S el_T_t;
      ignore @@ PsC.morph_expand yps_S yps_T m;
      res := AMap.add arr m !res
    )
    CategoryCat.Cat.arrows ;
  !res

let cat1 =
  let ps = PsC.ps_empty' () in
  PsC.add_el' ps CategoryCat.Cat.C1 @@ PsC.SGen.fresh_gen @@ "y(C1)";
  let ctxt = PsC.create_ctxt ps in
  PsC.ctxt_compute_ortho CategoryCat.ortho_maps ctxt;
  PsC.ctxt_get_ps ctxt

let prod_ress =
  let res = ref OMap.empty in
  List.iter (fun o ->
      let (ps,_) = OMap.find o yoneda_ps in
      res := OMap.add o (PsC.compute_prod cat1 ps) !res
    )
    CategoryCat.Cat.objects ;
  !res

let prod_maps =
  let res = ref AMap.empty in
  List.iter
    (fun arr ->
       let oS = CategoryCat.Cat.src arr in
       let oT = CategoryCat.Cat.tgt arr in
       let (psS,_) = OMap.find oS yoneda_ps in
       let (psT,_) = OMap.find oT yoneda_ps in
       let mST = AMap.find arr yoneda_maps in
       let prod_w_S = OMap.find oS prod_ress in
       let prod_w_T = OMap.find oT prod_ress in
       let mC1S_C1T = PsC.compute_prod_map_r cat1 psS psT mST prod_w_S prod_w_T in
       res := AMap.add arr mC1S_C1T !res
    )
    CategoryCat.Cat.arrows;
  !res

let presFunct = let open CategoryCat.Cat in
  {
    FP.obj_map = (fun o ->
        let p_res = OMap.find o prod_ress in
        PsC.prod_res_get_ps p_res
      ) ;
    FP.map_map = fun a ->
      AMap.find a prod_maps
  }

let _ =
  match FP.is_left_adjoint presFunct with
  | false -> Format.printf "Inconclusive left adjoint test.@."
  | true -> Format.printf "It is a left adjoint.@."
