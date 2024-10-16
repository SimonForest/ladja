# Description

`ladja` is a library providing computer assistance to show that a functor is a left adjoint.

# Examples

Several of considered categories and functors can be founds in the `categories/` and `functors/` folders.

The code checking that the functors defined in `functors/` are left adjoints can
be compiled with
```shell
make
```
producing programs `[name].byte` at the root from the files `[name].byte` in the
`functors/` folder.

Among examples of categories, there is:
- `setCat.ml`, encoding the category Set of sets,
- `pairCat.ml`, encoding the category Set × Set of products of sets,
- `categoryCat.ml`, encoding the category Cat of small categories.

Among examples of functors, there is:
- `truncation_functor.ml`, encoding the functor mapping a small category to its
  set of objects,
- `product_w_C1_functor.ml`, encoding the functor mapping a small category to
  its product with the walking arrow. For now, fully automated method fails for
  this example, and this code does not terminate,
- `product_w_C1_functor_unitl_assoc_only.ml`, which is basically the previous
  example where we only verify two out of four conditions for the functor to be
  a left adjoint,
- `pair_functor.ml`, encoding the product functor (X,Y) -> X × Y of sets (not a
  left adjoint, but provides an example where the criterion used is not
  satisfied).
