# TimeWeakFTC

## Result

`weakDeriv_primitive` is a generic one-dimensional weak fundamental theorem for curves valued in
a finite-dimensional real normed space.  If `p` and `q` are integrable on `(a,b)` and scalar
compactly supported smooth tests satisfy the vector-valued distributional identity `p' = q`, then
`p` agrees almost everywhere with `c + ∫_a^t q` for some constant vector `c`.

The statement uses only `NormedAddCommGroup`, `NormedSpace ℝ`, and `FiniteDimensional ℝ`; an
inner-product hypothesis is not needed.

## Route

The native De Giorgi module already contains the scalar theorem
`DeGiorgi.w11_ae_eq_ac_representative`, proved from the smooth-test fundamental lemma and a
Du Bois--Reymond argument.  The new theorem reuses it coordinatewise through the canonical
`Module.finBasis`.  Continuous coordinate maps commute with Bochner and interval integrals, and
finite-dimensional basis extensionality reassembles the vector conclusion.  No duplicate cutoff,
antiderivative, or distribution API was introduced.

## Verification

Focused verification passes without warnings or placeholders.  The source contains no `sorry`,
`admit`, or new axiom.

## Project position

The generic theorem and its dedicated coordinate-reduction machinery are complete (100%).  No
L-geometry consumer was edited here, so applying the theorem to the post-density L-action weak
Euler identity remains 0% in this lane.  This closes one small generic analytic gate and does not
by itself change the live project estimates: the minimizer/direct-method machinery remains roughly
72--78%, dedicated L-geometry roughly 73--77%, `redVolume_anti` 0%, P2 below 1%, and the whole
Poincare program roughly 3--5%.
