all:
	ocamlbuild functors/truncation_functor.byte
# ^ the example of the truncation functor Cat -> Set
# ocamlbuild functors/product_w_C1_functor.byte
# ^ an example with the functor (C : Cat) |-> C x 2
# SF: some optimisations are still needed
	ocamlbuild functors/product_w_C1_functor_unitl_assoc_only.byte
# ^ the same functor as before with partial automated verification of the
# criterion
	ocamlbuild functors/pair_functor.byte
# ^ a non-example with the non-left-adjoint product functor (X,Y) |-> X x Y

clean:
	rm -r _build
	rm *.byte
