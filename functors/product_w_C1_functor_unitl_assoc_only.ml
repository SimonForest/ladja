module ST = CategoryCat
module TT = CategoryCat
module FP = Lib2.FunctorPres(ST)(TT)

module PsC = FP.SourceTheory.Ps
module PsCT = FP.TargetTheory.Ps

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
      let (_,_,el_T_t) = PsC.arr_to_map' yps_T arr yel_T in
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

let ctxt_check_iso ctxtA ctxtB morph =
  let psA = TT.Ps.ctxt_get_ps ctxtA in
  let psB = TT.Ps.ctxt_get_ps ctxtB in
  TT.Ps.check_iso psA psB morph


let _ =
  match CategoryCat.ortho_maps with
  | [o_unitl;o_unitr;o_assoc;o_pair] ->
    let _ = (* check o_unitl *)
      Format.printf "First goal: show that o_unitl is sent to an isomorphism.@\n";
      let (psA,psB,mF) = o_unitl in
      let imA_infos = FP.ps_obj_map presFunct psA in
      let imB_infos = FP.ps_obj_map presFunct psB in
      let im_mF = FP.ps_map_map presFunct psA psB mF imA_infos imB_infos in
      let ctxt_imA = CategoryCat.Ps.create_ctxt imA_infos.ps in
      let ctxt_imB = TT.Ps.create_ctxt imB_infos.ps in
      (* T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imA; *)
      (* T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imB; *)
      (* let im_mF_ortho = T.Ps.ctxt_compute_ortho_map TargetTheory.ortho_maps ctxt_imA ctxt_imB im_mF in *)
      Format.printf "Image presheaf of A:@\n";
      TT.Ps.print_ps_elts' (TT.Ps.ctxt_get_ps ctxt_imA);
      Format.printf "Image presheaf of B:@\n";
      TT.Ps.print_ps_elts' (TT.Ps.ctxt_get_ps ctxt_imB);
      Format.printf "Image morphism of g: A->B:@\n";
      TT.Ps.print_morph im_mF;
      Format.printf "@]@]";
      let cii = TT.Ps.check_iso
          (TT.Ps.ctxt_get_ps ctxt_imA)
          (TT.Ps.ctxt_get_ps ctxt_imB)
          im_mF in
      TT.Ps.print_check_iso cii;
      Format.printf "Try: manual method for getting isomorphism.@\n";
      TT.Ps.ctxt_enforce_ex_lifting_step [o_unitl] ctxt_imA;
      TT.Ps.ctxt_presheaf_interleaved ctxt_imA;
      TT.Ps.ctxt_presheaf_interleaved ctxt_imB;
      let im_mF_ortho = TT.Ps.ctxt_compute_ortho_map [o_unitl] ctxt_imA ctxt_imB im_mF in
      begin
        if TT.Ps.morph_is_iso (TT.Ps.ctxt_get_ps ctxt_imA) (TT.Ps.ctxt_get_ps ctxt_imB) im_mF_ortho then
          Format.printf "Success: o_unitl is sent to an isomorphism.@\n"
        else
          Format.printf "Failure: inconclusive method.@\n";
      end
    in
    Format.printf "@\n@\n";
    let _ = (* check o_assoc *)
      Format.printf "Second goal: show that o_assoc is sent to an isomorphism.@\n";
      let (psA,psB,mF) = o_assoc in
      let imA_infos = FP.ps_obj_map presFunct psA in
      let imB_infos = FP.ps_obj_map presFunct psB in
      let im_mF = FP.ps_map_map presFunct psA psB mF imA_infos imB_infos in
      let ctxt_imA = CategoryCat.Ps.create_ctxt imA_infos.ps in
      let ctxt_imB = TT.Ps.create_ctxt imB_infos.ps in
      (* T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imA; *)
      (* T.Ps.ctxt_compute_ortho TargetTheory.ortho_maps ctxt_imB; *)
      (* let im_mF_ortho = T.Ps.ctxt_compute_ortho_map TargetTheory.ortho_maps ctxt_imA ctxt_imB im_mF in *)
      Format.printf "Image presheaf of A:@\n";
      TT.Ps.print_ps_elts' (TT.Ps.ctxt_get_ps ctxt_imA);
      Format.printf "Image presheaf of B:@\n";
      TT.Ps.print_ps_elts' (TT.Ps.ctxt_get_ps ctxt_imB);
      Format.printf "Image morphism of g: A->B:@\n";
      TT.Ps.print_morph im_mF;
      Format.printf "@]@]";
      let cii = TT.Ps.check_iso
          (TT.Ps.ctxt_get_ps ctxt_imA)
          (TT.Ps.ctxt_get_ps ctxt_imB)
          im_mF in
      TT.Ps.print_check_iso cii;
      Format.printf "Try: manual method for getting isomorphism.@\n";
      TT.Ps.ctxt_enforce_ex_lifting_step [o_assoc] ctxt_imA;
      TT.Ps.ctxt_presheaf_interleaved ctxt_imA;
      TT.Ps.ctxt_presheaf_interleaved ctxt_imB;
      let im_mF_ortho = TT.Ps.ctxt_compute_ortho_map [o_assoc] ctxt_imA ctxt_imB im_mF in
      begin
        if TT.Ps.morph_is_iso (TT.Ps.ctxt_get_ps ctxt_imA) (TT.Ps.ctxt_get_ps ctxt_imB) im_mF_ortho then
          Format.printf "Success: o_assoc is sent to an isomorphism.@\n"
        else
          Format.printf "Failure: inconclusive method.@\n";
      end
    in
    ()
  | _ -> failwith "ortho_maps of CategoryCat not up-to-date."

(* let _ = *)
(*   match FP.is_left_adjoint presFunct with *)
(*   | false -> Format.printf "Inconclusive left adjoint test.@." *)
(*   | true -> Format.printf "It is a left adjoint.@." *)
