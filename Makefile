all:
	ocamlbuild functors/pair_functor.byte
	ocamlbuild functors/truncation_functor.byte
# ocamlbuild functors/product_w_C1_functor.byte
# SF: ^ still some debugging to do for the last one
