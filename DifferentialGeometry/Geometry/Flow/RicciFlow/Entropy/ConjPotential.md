# Conjugate-heat potential

## Goal

Realize the lower-order term in the forward time-reversed conjugate heat
equation as the genuine family

`A1(s) = multiplication by -R(T-s) : H¹(gT) →L H⁰(gT)`.

There is no drift term and no moving-measure conjugation in this fixed-reference
formulation.  The connection-difference times gradient contribution already
belongs to the completed moving-Laplacian operator `A2`.

## Route

`conjCoeff` bundles the fixed-time smooth scalar coefficient `-R(t)`.
`conjA1` applies the fixed-metric multiplier `scalarPotH0`.  Operator-norm
continuity follows from `scalar_unif` and the pointwise pairwise multiplier
bound.  Compactness bounds the terminal scalar curvature, while the same
uniform time modulus gives a short-interval bound for every reflected slice.

`conjCoeff_joint` now reduces joint smoothness of the coefficient directly to
the geometric producer `scalar_joint`.  That producer uses actual local
coordinate-frame domains and the Ricci-flow identity
`Ric = -1/2 * ∂ₜ g`; it does not add a global chart selector or a
consumer-side smoothness assumption.

`conjCoeff_rev` is the orientation adapter used by the forward reversed-time
problem.  It composes `conjCoeff_joint` with the smooth map
`(x, s) ↦ (T - s, x)` and restricts exactly to reflected regular times.  It
adds no assumptions or independent regularity package.

The direct lambda-valued theorem statement timed out deterministically at
`whnf`, even with 800k heartbeats; removing the `omit` wrapper did not help.
Naming the ordinary scalar map as the opaque `conjCoeffRev : M × ℝ → ℝ`
made the statement cheap, while the proof unfolds it only after the scalar
composition is formed.  Restoring the weakest-assumption `omit` wrapper then
passed without a warning.

## Verification status

The existing operator results and both joint coefficient theorems pass focused
verification.  The opaque scalar-map normal form reduced the focused check from
a deterministic timeout to a clean pass.  The named-module export now also
passes.

`conjCoeff_bound` exports the pointwise estimate that was previously buried in
the proof of `conjA1_short`: on one nontrivial closed reversed-time interval,
the absolute scalar coefficient is bounded by a single nonnegative constant,
uniformly in space.  Its proof uses `scalar_unif` and compactness of the
terminal scalar-curvature range; it adds no consumer assumption.  Focused and
targeted verification pass without local warnings.

## Progress accounting

- A2 short-time measurable input: complete (100%).
- A1 operator and `conjA1_short`: complete (100%).
- `conjCoeff_joint` and `conjCoeff_rev`: theorem and dedicated geometric
  producer machinery complete (100%), focused verified.
- `conjCoeff_bound`: theorem and dedicated pointwise-bound machinery complete
  (100%), focused and targeted verified.
- The uniform scalar-multiplier jet and finite-pairing producers are now also
  complete (100%); they remain machinery, not the final conjugate-heat theorem.
- The separate genuine A2/A1 input producers and their dedicated machinery:
  complete (100%); `ConjStrong.conj_strong_exists` now completes their
  specialized spectral strong-solution assembly (100%).
- The Galerkin classical moving-metric conjugate-heat existence theorem is
  complete in `ConjGalerkinClassical.lean`; the separate
  `heatpot_of_maxreg` route remains theorem-level 0%.
- Perelman no-local-collapsing theorem: not proved (0%).
