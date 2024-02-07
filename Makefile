all:
	ocamlbuild functors/truncation_functor.byte
# ^ the example of the truncation functor Cat -> Set
	ocamlbuild functors/pair_functor.byte
# ^ a non-example with the non-left-adjoint pair functor (X,Y) |-> X x Y
# ocamlbuild functors/product_w_C1_functor.byte
# SF: ^ still some debugging to do for the last one
