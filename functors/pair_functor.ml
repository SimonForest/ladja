module FP = Lib2.FunctorPres(PairCat)(SetCat)

module PsPC = FP.SourceTheory.Ps
module PsSC = FP.TargetTheory.Ps

let psL = PsSC.ps_empty' ()

let psR = PsSC.ps_empty' ()

let psP = PsSC.ps_empty' ()
let ast = PsSC.SGen.fresh_gen "*"
let _ =
  PsSC.add_el' psP SetCat.Cat.Ast ast

let mLP = PsSC.morph_empty ()
let mRP = PsSC.morph_empty ()

let presFunct = let open PairCat.Cat in
  {
    FP.obj_map = (function
      | L -> psL
      | R -> psR
      | P -> psP) ;
    FP.map_map = function
      | PiL -> mLP
      | PiR -> mRP
  }

let _ =
  match FP.is_left_adjoint presFunct with
  | false -> Format.printf "Inconclusive left adjoint test.@."
  | true -> Format.printf "It is a left adjoint.@."
