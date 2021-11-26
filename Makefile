all:
	ocamlbuild functors/pair_functor.byte
	ocamlbuild functors/product_w_C1_functor.byte
	ocamlbuild functors/truncation_functor.byte
