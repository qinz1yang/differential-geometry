# Potential evolution

## 2026-07-16

`PotentialEvolution.lean` proves `potential_pde`.  For a classical solution

`partial_s u = Delta u + V u`

and a positive spatial slice at a time `s > 0`, the reconstructed potential
`f = -log (u / (4*pi*s)^(-n/2))` satisfies the intrinsic pointwise equation

`partial_s f = Delta f - <grad f, grad f> - V - n/(2*s)`.

Thus the reversed conjugate-heat specialization `V = -R` has the expected
`+R` term.  The statement is deliberately local at one regular time: it asks
only for positivity of that spatial slice, not positivity on a whole time
carrier.  It also relies on the canonical tangent-bundle instance and exports
no `VectorBundle`, chart-selection, compactness, boundary, or extra regularity
assumption.

The proof separates into two scalar identities.  Spatially, slice smoothness
feeds `gradientFun_log` and `laplacian_log`; spatial constants are removed with
the existing gradient/Laplacian linearity rules.  In time, the heat equation
and `perelmanDensityPrefactor_hasDerivAt` differentiate the quotient directly,
then the logarithmic derivative and scalar field algebra give the displayed
coefficient.  No tensor-fiber equality or coordinate frame is introduced.

Focused verification passed without local warnings or `sorry`.  The first
check was blocked only by missing stale upstream object files; narrow explicit
module refreshes restored the import chain before proof checking.

`potential_df_time` is now also complete.  On
`D.regular ∩ Set.Ioi 0`, positivity of the actual heat-potential producer and
joint smoothness give joint `C²` regularity of the reconstructed potential.
The proof keeps the calculation scalar: it proves smoothness of the positive
prefactor with `Real.contDiffAt_rpow_const_of_ne`, forms the scalar quotient and
logarithm, and then applies `fixedBaseOnRegSmooth`.  The resulting theorem says
that the time derivative of `extDerivFun f` at a fixed base point and tangent
vector is `extDerivFun` of the displayed `potential_pde` velocity.  The
carrier-within derivative is upgraded at the final regular time using
`D.regular_mem_nhds`.

This closes the mixed time/space derivative input required by
`normGradSq_time`.  It introduces no frame, whole-Hom equality, chart-selection
assumption, or new consumer predicate; the theorem-local boundaryless instance
is exactly the existing requirement of `fixedBaseOnRegSmooth`.  Focused
verification passed without local warnings or `sorry`.

`potential_joint` now packages the same scalar rpow/quotient/log argument at
order infinity.  It proves joint spacetime smoothness on
`(D.regular ∩ Ioi 0) × univ` directly from `IsHeatPotOn.jointSmooth` and the
existing positivity hypothesis.  This is the regularity producer needed by
the moving-volume `W` calculation; it does not ask the final consumer for a
separate smoothness witness.  Focused verification passed without warnings or
new `sorry`.

Accounting: `potential_pde`, `potential_df_time`, and `potential_joint` are
complete (100% each).  The concrete reversed-flow scalar and gradient-square
derivatives are also complete in `FlowVariation.lean`, and
`WVariation.w_rev_hasDerivAt` now gives the checked interval-local raw
first-variation theorem.  Weighted square completion, `W` monotonicity,
Perelman no-local-collapsing, and the HCG endpoint remain theorem-level 0%.
Broader entropy/noncollapse machinery is approximately 67%; endpoint progress
is not inferred from that infrastructure percentage.

The downstream square assembly is now checked: `weighted_w_square` and
`w_rev_deriv_nonpos` consume this slice theorem without asking for a separate
smoothness witness.  The potential evolution producers remain 100%; this note
does not count their downstream use as completion of Perelman
no-local-collapsing, which remains theorem-level 0%.

The local gradient and squared-gradient calculations formerly duplicated
inside `potential_pde` now reuse `PotentialGeometry.potential_grad_sq`.
Focused verification of the consumer passed after this extraction; its public
statement and assumptions are unchanged.
