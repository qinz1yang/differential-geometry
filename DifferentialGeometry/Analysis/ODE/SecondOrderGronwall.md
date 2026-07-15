# SecondOrderGronwall

## 2026-07-07 V1c quantitative endpoint corollaries

Status: `SecondOrderGronwall.lean` now has fixed-normed-space quantitative
endpoint wrappers for the perturbation estimate.

Completed:

- Added `gronwallBound_zero_mono_eps`: for `K, x >= 0`, the zero-initial
  Gronwall bound is monotone in the inhomogeneous amplitude `eps`.
- Added `gronwall_le_linear`: if `Y 0 = 0`, `Y' 0 = w`, and
  `‖Y''‖ ≤ K‖Y‖`, then `‖Y t‖` is bounded above by the linear term
  `t * ‖w‖` plus the existing Gronwall error.
- Added `gronwall_ge_linear`: under the same hypotheses, `‖Y t‖` is bounded
  below by the linear term minus the existing Gronwall error.

Route:

- Both wrappers are direct corollaries of `gronwall_sub_linear` using only the
  triangle inequality and `‖t • w‖ = t * ‖w‖` on `t ∈ Icc 0 b`.
- The epsilon-monotonicity lemma is a direct scalar consequence of the
  Mathlib definition of `gronwallBound`; it is used to replace per-field
  Gronwall amplitudes by a uniform upper amplitude.
- These are the ODE-layer quantitative producers needed before a covariant
  parallel-frame transfer can give endpoint length or singular-value bounds for
  radial Jacobi fields.

Current blocker / next frontier:

- The V1c radial-Jacobi determinant theorem is still not started.  These lemmas
  live in a fixed normed vector space; the remaining producer must transport the
  radial Jacobi field through a parallel orthonormal frame and discharge the
  `covGronwall` differentiability, ODE-bound, and initial-condition hypotheses.

Progress estimates:

- `gronwallBound_zero_mono_eps`: 100% complete as a scalar monotonicity bridge.
- `gronwall_le_linear`: 100% complete as a fixed-space ODE endpoint upper
  wrapper.
- `gronwall_ge_linear`: 100% complete as a fixed-space ODE endpoint lower
  wrapper.
- V1c Gronwall producer infrastructure: about 20% complete; the scalar ODE
  endpoint estimates exist, but the covariant/radial-Jacobi instantiation is
  still missing.
- V1c two-sided determinant theorem: 0% complete; no capped-scale theorem is
  stated yet.
- Stage V1: about 48% complete after the ODE endpoint wrappers, V1c algebraic
  consumers, and V1d shell work.
- Whole volume-comparison lane: about 27% complete; V0, V1a, endpoint V1b,
  V1c algebraic consumers, one fixed-space Gronwall producer brick, and V1d
  conditional integration shells are in place, but covariant Gronwall
  comparison, explicit capped constants, and the final two-sided theorem remain.

Verification: focused verification and targeted module verification passed for
`SecondOrderGronwall.lean`.
Targeted downstream verification passed for
`DifferentialGeometry.Geometry.Comparison.Variation.CovariantGronwall`,
`DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall`,
`DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds`, and
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`; only existing
upstream/downstream warnings were replayed.

## 2026-07-08 zero-initial epsilon scaling

Completed:

- Added `gronwallBound_zero_mul_eps`: with zero initial data, `gronwallBound`
  is exactly linear in the inhomogeneous amplitude.  This is the scalar bridge
  needed by the lower radial-Jacobi scaled-radius route, where the initial
  direction is replaced by `a • w` and the Gronwall error must scale by the
  same positive factor.

Current blocker / next frontier:

- This is only scalar ODE algebra.  The final V1c lower determinant route still
  needs the radial analytic package and a usable unscaled scalar lower model
  comparison for unit coefficient directions.

Progress estimates:

- `gronwallBound_zero_mul_eps`: 100% complete as a zero-initial scalar scaling
  bridge.
- V1c Gronwall producer infrastructure: about 21% complete at the scalar ODE
  layer; the new lemma helps the radial lower scaled route but does not produce
  geometric regularity or curvature inputs.

Verification: focused verification and targeted module verification passed for
`SecondOrderGronwall.lean`.  Targeted downstream verification also passed for
`DifferentialGeometry.Geometry.Comparison.Variation.CovariantGronwall`,
`DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall`,
`DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds`, and
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.

## 2026-07-08 positive scalar smallness

Completed:

- Added `exists_gron_small`: if `B0 > 0` and `K,D >= 0`, then one can choose
  `b > 0` and `B > 0` so that
  `B <= B0 - gronwallBound 0 (max K 1) (K * (b * D)) 1`.

Route:

- This is pure scalar algebra.  It writes the zero-initial Gronwall error at
  `x = 1` as a linear function of `b`, then chooses `b` small enough that the
  error is at most `B0 / 2`.

Current blocker / next frontier:

- The scalar smallness choice is now available.  The lower radial route still
  needs the geometric analytic package: radial regularity, a parallel frame,
  `chartRepAt` differentiability, ODE/curvature bounds, and the Jacobi
  initial-derivative bridge.

Progress estimates:

- `exists_gron_small`: 100% complete as a scalar existence lemma.
- V1c Gronwall producer infrastructure: about 22% complete at the scalar ODE
  layer; this closes the scalar smallness choice but does not produce the
  radial analytic hypotheses.

Verification: focused verification and targeted module verification passed for
`SecondOrderGronwall.lean`.  Targeted downstream verification also passed for
`DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall`,
`DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds`, and
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume`.

## 2026-07-08 time-one small coefficient

Completed:

- Added `exists_gron_smallK`: if `B0 > 0` and `D >= 0`, then one can choose
  `K > 0` and `B > 0` so every `0 <= k <= K` satisfies
  `B <= B0 - gronwallBound 0 (max k 1) (k * D) 1`.

Route:

- This is pure scalar algebra at endpoint time `1`.  For `k <= 1`,
  `max k 1 = 1`, so the zero-initial Gronwall error is linear in `k` with
  coefficient `D * (exp 1 - 1)`.  The proof chooses the coefficient cap small
  enough to keep the error below `B0 / 2`.

Current blocker / next frontier:

- This closes the scalar small-`K` choice only.  Downstream volume wrappers
  still need an upper scalar compatibility inequality for the same endpoint
  constant `B`, and the final capped volume theorem remains unstated.

Progress estimates:

- `exists_gron_smallK`: 100% complete as a time-one scalar smallness bridge.
- V1c Gronwall producer infrastructure: about 99.85% complete at the current
  scalar/producer layer; final determinant and capped volume endpoints remain
  separate 0% theorems.

Verification passed for focused `SecondOrderGronwall.lean`.  Targeted refresh
of `DifferentialGeometry.Analysis.ODE.SecondOrderGronwall` passed before
downstream consumption.
