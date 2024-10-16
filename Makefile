all:
	ocamlbuild functors/truncation_functor.byte
# ^ the example of the truncation functor Cat -> Set
	ocamlbuild functors/pair_functor.byte
# ^ a non-example with the non-left-adjoint pair functor (X,Y) |-> X x Y
	ocamlbuild functors/product_w_C1_functor_unitl_assoc_only.byte
# ^ a non-example with the non-left-adjoint pair functor (X,Y) |-> X x Y
# ocamlbuild functors/product_w_C1_functor.byte
# SF: ^ example for which some optimisation is needed

clean:
	rm -r _build
	rm *.byte
