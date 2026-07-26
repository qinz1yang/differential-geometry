# NormGradSqTime.lean

## Result

`gradSq_joint` proves that the spacetime scalar

`(s, x) ↦ g(s)(∇^{g(s)} f(s), ∇^{g(s)} f(s))`

is jointly `C∞` on `U × M` from joint `C∞` of `f` and of the moving
chart-Gram entries on the same open time set `U`.  Its metric input is the
all-real `RealizedMetricFamily`; it does not require an interval family or a
`MetricFamilySmoothOn` package.  The chart-Gram hypothesis is deliberately in
the exact normal form produced by `revGram_smooth`.

`normGradSq_time` proves the invariant pointwise identity

`∂ₜ |∇f|² = 2 Q(∇f, ∇f) + 2 g(∇ft, ∇f)`

under `∂ₜg = -2Q` and the scalar slot derivative `∂ₜ(df) = dft`.  Its public
statement contains no tangent basis, inverse-metric components, local chart,
or tensor-component realization data.  It also needs only finite-dimensionality
of the model and the existing smooth-manifold instance; lower-order manifold
instances and `Module.Finite` are not exported as consumer assumptions.

## Proof route

For `gradSq_joint`, center one genuine chart trivialization at the point under
consideration and fully scalarize.  The chart-Gram entries are smooth by the
input hypothesis, the spatial components of `df` are smooth by
`prodExtDerivAt_inf`, and Cramer's rule makes each inverse-Gram entry smooth.
The finite contraction is then identified with the intrinsic cotangent norm
and hence with the squared gradient norm.  Positive-definiteness of the actual
chart Gram matrix supplies the nonzero determinant.  The proof never compares
dependent tensor fibers or whole Hom objects and uses no globally selected
frame or `HasLocallyConstantChartAt`.

The theorem realizes `df` with `differential1FormFun`, applies the invariant
rank-one theorem `normSq_one_time`, and then uses scalar pairing identities to
identify `cotangentSharp (df)` with `gradientFun`.  All equalities are fully
evaluated tangent-pairing or real-valued equalities.  No whole-Hom equality and
no locally constant chart selector is used.

The only failed local attempt was an over-eager repeated rewrite of the same
sharp identity: one rewrite already handled both equal occurrences in the norm
term, while the mixed term required the two explicit specializations.  This was
a local rewrite-shape issue, not an API or mathematical obstruction.

## Verification

Focused verification of both public theorems is GREEN, with no `sorry` and no
local warning.

## Honest project position

- `normGradSq_time`: complete (100%).
- `gradSq_joint`: complete (100%).
- Dedicated generic joint-regularity machinery for the moving gradient square:
  complete (100%).
- Its dedicated low-level rank-one machinery (`basisInv_time`, `ricReact_one`,
  and `normSq_one_time`): complete (100%).
- Raw reversed-flow W-functional assembly is now checked in
  `Entropy/WVariation.lean`: `w_rev_hasDerivAt` is complete (100%).
- Weighted square completion and W monotonicity remain separate theorem-level
  frontiers at 0%.
- Perelman's no-local-collapsing endpoint theorem: unstated/unproved (0%).
- Broader entropy/noncollapsing machinery: approximately 67%.
- Whole HCG compactness project: about 60%.
