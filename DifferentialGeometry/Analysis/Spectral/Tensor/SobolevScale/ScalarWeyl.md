# ScalarWeyl

## Status

`scalar_diag_le` and `scalar_eigen_tail` are implemented and focused
verification passes without warnings.

The proof uses the existing rank-zero point-evaluation Sobolev estimate on a
finite self-reproducing spectral combination.  Orthogonality identifies its
Sobolev norm with the weighted diagonal sum; integrating the resulting
pointwise estimate gives the scalar counting bound and hence the required
eigenvalue-tail summability.

This is the narrow scalar producer needed by the conjugate-heat Galerkin
consumers.  It does not prove the stronger generic tensor local-Weyl theorem,
and it adds no geometric or spectral assumption.  The theorem itself and its
dedicated machinery are both complete; consumer rewiring is tracked in the
conjugate-Galerkin notes.

The exact module artifact refresh passed.  The axiom audit for
`scalar_eigen_tail` reports only `propext`, `Classical.choice`, and
`Quot.sound`; in particular it does not contain `sorryAx`.
