# ChristoffelPerturbation

## 2026-07-14 uniform first-order coefficient estimates

The file now provides family-uniform perturbation and absolute bounds for the
inverse Gram derivative, Christoffel symbols, and first coordinate derivatives
of Christoffel symbols.  The principal producers are
`invGramD_pou_lip`, `christoffel_pou_lip`, `christoffelD_pou_lip`,
`christoffel_pou_bnd`, and `christoffelD_pou_bnd`.

The proofs use the inverse-matrix derivative identity and finite coordinate
sums; no compactness choice depends on the family index.  Focused and targeted
verification passed.

These estimates supply lower-order coefficients for Ricci and the DeTurck Lie
term.  They do not supply the low-regularity parabolic solver.
