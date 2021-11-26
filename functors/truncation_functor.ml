module FP = Lib2.FunctorPres(CategoryCat)(SetCat)

module PsCC = FP.SourceTheory.Ps
module PsSC = FP.TargetTheory.Ps


let psImgC0 = PsSC.ps_empty' ()
let ast00 = PsSC.SGen.fresh_gen "*0"
let _ =
  PsSC.add_el' psImgC0 SetCat.Cat.Ast ast00

let psImgC1 = PsSC.ps_empty' ()
let ast10 = PsSC.SGen.fresh_gen "*0"
let ast11 = PsSC.SGen.fresh_gen "*1"
let _ =
  PsSC.add_el' psImgC1 SetCat.Cat.Ast ast10;
  PsSC.add_el' psImgC1 SetCat.Cat.Ast ast11

let psImgC12 = PsSC.ps_empty' ()
let ast20 = PsSC.SGen.fresh_gen "*0"
let ast21 = PsSC.SGen.fresh_gen "*1"
let ast22 = PsSC.SGen.fresh_gen "*2"
let _ =
  PsSC.add_el' psImgC12 SetCat.Cat.Ast ast20;
  PsSC.add_el' psImgC12 SetCat.Cat.Ast ast21;
  PsSC.add_el' psImgC12 SetCat.Cat.Ast ast22


let mImgDminus = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgDminus SetCat.Cat.Ast ast00 ast10

let mImgDplus = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgDplus SetCat.Cat.Ast ast00 ast11

let mImgId = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgId SetCat.Cat.Ast ast10 ast00;
  PsSC.morph_add mImgId SetCat.Cat.Ast ast11 ast00

let mImgPiL = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgPiL SetCat.Cat.Ast ast10 ast20;
  PsSC.morph_add mImgPiL SetCat.Cat.Ast ast11 ast21

let mImgPiR = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgPiR SetCat.Cat.Ast ast10 ast21;
  PsSC.morph_add mImgPiR SetCat.Cat.Ast ast11 ast22

let mImgComp = PsSC.morph_empty ()
let _ =
  PsSC.morph_add mImgComp SetCat.Cat.Ast ast10 ast20;
  PsSC.morph_add mImgComp SetCat.Cat.Ast ast11 ast22

let presFunct = let open PairCat.Cat in
  {
    FP.obj_map = (function
      | C0 -> psImgC0
      | C1 -> psImgC1
      | C12 -> psImgC12) ;
    FP.map_map = function
      | Dminus -> mImgDminus
      | Dplus -> mImgDplus
      | Id -> mImgId
      | PiL -> mImgPiL
      | PiR -> mImgPiR
      | Comp -> mImgComp
  }

let _ =
  match FP.is_left_adjoint presFunct with
  | false -> Format.printf "Inconclusive left adjoint test.@."
  | true -> Format.printf "It is a left adjoint.@."
