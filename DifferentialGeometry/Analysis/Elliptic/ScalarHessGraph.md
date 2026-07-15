# ScalarHessGraph

## 2026-07-10

- Added the chart-locality-free theorem `scalar_hess_graph`.
- The theorem is stated in the uniform normal form `∃ C, ∀ f`: the metric-only
  constant is chosen before the smooth scalar field.  An earlier local draft had
  `f` outside the existential, which proved the right estimate but exposed only
  the logically weaker `∀ f, ∃ C` interface; that quantifier order was corrected
  before downstream use.
- It integrates the unconditional scalar Bochner identity, uses Green's first
  identity to replace the gradient--Laplacian cross term by minus the Laplacian
  energy, and uses `exists_ricci_bound` for the metric-only Ricci coefficient.
- The resulting constant depends only on the fixed smooth metric and is uniform
  over all smooth scalar fields; in particular it is independent of spectral
  support and support cardinality.
- Focused verification passed without warnings.
- Targeted module verification passed.
- This closes the scalar Bochner/Green analytic estimate in its cheapest native
  normal form.  The next A2 step is to combine `hess_sub_conn` with intrinsic
  trace linearity, then bound the two trace terms against these scalar Hessian
  and gradient energies.
