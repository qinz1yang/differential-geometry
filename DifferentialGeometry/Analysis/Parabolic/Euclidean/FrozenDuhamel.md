# FrozenDuhamel

## Scope

This file is the dimension-generic dense analytic core for the frozen
Euclidean Duhamel realization needed by the low-regularity Ricci--DeTurck
parametrix.  It is not an endpoint wrapper.

## Current source state

- `lapEval` and `coreLap` package the orthonormal trace of a bounded realized
  second Frechet derivative without adding a new class or instance.
- `heatSup_scaled` rewrites the positive-time heat convolution against the
  fixed time-one Gaussian.
- `heatScaled_cont` and `heatSup_zero` provide the positive-time continuity
  and quantitative right limit at time zero needed for the genuine boundary
  term.
- `heatScaled_time` differentiates that representation at positive time.  Its
  domination uses the finite first Gaussian moment and boundedness of the
  realized first derivative; it does not assume the desired heat equation.
- `scaledDt_eq_lap` is the orthonormal-basis integration-by-parts identity,
  and `heatSup_time` combines it with differentiation to obtain the actual
  positive-time heat equation.
- `heatSup_primitive` uses the quantitative zero-time limit and the Banach
  FTC to prove the fundamental semigroup primitive identity with the correct
  endpoint value.
- `frozenDuh` is the time-reversed simple-tensor Duhamel integral.  The
  private Volterra lemma splits off the moving sliver and proves it is
  quadratic when the coefficient vanishes at zero; the general boundary
  term is then recovered by subtracting the coefficient's value at zero.
- `frozenDuh_space` realizes the spatial jet under the time integral.
  Applying it to `(u, du)` and `(du, d2u)` gives the value, gradient, and
  Hessian chain without extra spatial derivatives.
- `frozenDuh_time` combines the Volterra derivative with one interval
  integration by parts and the positive-time heat equation.
- `frozenDuh_pde` is the complete isotropic zero-trace producer:
  `∂t frozenDuh = lapEval (D² frozenDuh) + a(t)u`, together with the two
  realized spatial-jet statements.
- `FrozenDuhamelSPD.lean` is the separate fixed-SPD conjugation layer.

## Verification

The source was written while the shared Edge lane owned the sole Lean build
slot.  No Lean command has yet been run on this file; focused verification is
therefore pending explicit release of that slot.  There is no `sorry`,
`admit`, axiom, opaque placeholder, or assumed PDE in this source.  All
percentages below are therefore source-level only and must not be read as a
proved Lean result.

## Honest progress

- Exact endpoint `ricci_flow_unif_existence`: **0%** (unchanged).
- Isotropic frozen zero-trace Duhamel theorem: **100% source-level**, **0%
  verified**.
- Positive-time fixed-Gaussian differentiation and PDE machinery: **100%
  source-level**, **0% verified**.
- Fixed-SPD conjugation and consumer-visible jets: **100% source-level** in
  `FrozenDuhamelSPD.lean`, **0% verified**.

The exact next action is focused Lean verification of `FrozenDuhamel.lean`
after the shared build slot is explicitly released.  Expected work is
elaboration repair in the fixed-Gaussian integration-by-parts and Volterra
quadratic-sliver proofs, not another mathematical producer.
