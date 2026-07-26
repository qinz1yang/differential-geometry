# CovariantGronwall.lean — covariant Grönwall transfer (B3 keystone)

Verification passed, sorry-free (2026-06-11). Part of the Step A item-3a ladder
(`Comparison/ConvexBalls.md` B3; B0 stage-4 base).

2026-07-07 update: added `covGronwall_bounds`, a quantitative version of the
same parallel-frame transfer.  It gives both endpoint estimates
`sqrt(g(J,J)) ≤ t * sqrt(g(w,w)) + error` and
`t * sqrt(g(w,w)) - error ≤ sqrt(g(J,J))` under the same covariant ODE,
parallel-frame, differentiability, and initial-condition hypotheses, using the
fixed-space wrappers `gronwall_le_linear` / `gronwall_ge_linear`.

## `covGronwall_bounds`

Field `J` along `γ` with a second-order covariant bound
`g(D²J, D²J) ≤ K²·g(J,J)` on `Ico 0 b`, a **parallel `g`-ON frame `F` of full
cardinality** on `Icc 0 b`, ICs `J 0 = 0`, `D_tJ 0 = w`, and the usual
regularity hypotheses
⟹ for every `t ∈ Icc 0 b`, `sqrt(g(J,J))` is trapped between the linear term
`t * sqrt(g(w,w))` plus/minus the explicit Gronwall error.

This is now the V1c-facing quantitative transfer theorem.  It still does not
instantiate the radial Jacobi field or prove the curvature-bound input.

Verification: focused verification and targeted module verification passed for
`CovariantGronwall.lean`; local `show` style warnings in this file were cleaned.
Only existing upstream warnings were replayed.

## `covGronwall_ne_zero`

Field `J` along `γ` with a second-order covariant bound
`g(D²J, D²J) ≤ K²·g(J,J)` on `Ico 0 b`, a **parallel `g`-ON frame `F` of full
cardinality** on `Icc 0 b`, ICs `J 0 = 0`, `D_tJ 0 = w`, and the Grönwall
smallness `gronwallBound 0 (max K 1) (K·b·√g(w,w)) b < b·√g(w,w)`
⟹ `J b ≠ 0`.

Route: coefficients `yᵢ t = g(Fᵢ t, J t)` differentiate by
`metric_compat_hasDerivAt_inner` (parallel frame kills the `D_tF` terms), bundle
into `Y : ℝ → EuclideanSpace ℝ ι` via `(EuclideanSpace.equiv ι ℝ).symm` +
`hasDerivAt_pi` + `HasFDerivAt.comp_hasDerivAt`; the ℓ²-norm equals the `g`-norm
exactly (`inner_self_eq_sum_sq`, full ON frame), so `hODE` transports to
`‖Y''‖ ≤ K‖Y‖`; `gronwall_ne_zero` (SecondOrderGronwall) finishes; `Y b ≠ 0`
⟹ `J b ≠ 0` (coefficients of `0` vanish).

## Consumers / next bricks

Instantiate with the radial Jacobi field of `exp_p` (`Exponential/
JacobiVariation.lean`: `exists_radial_jacobi_radius` + ICs + endpoint
`J(1) = d(exp_p)w`) to get endpoint length/singular-value estimates via
`covGronwall_bounds`, and nonvanishing / `d(exp)_v` injectivity via
`covGronwall_ne_zero`, below the curvature scale.
REMAINING for that instantiation:
- the curvature-norm input `g(R(J,γ')γ', R(J,γ')γ') ≤ K²·g(J,J)` (b);
- a full parallel ON frame along the radial geodesic (PerpFrame gives the perp
  part; add the parallel unit velocity);
- chartRep-differentiability of the radial `J`, `D_tJ`, frame (regularity
  plumbing);
- **the `t = 0` gap**: the radial Jacobi equation is only available on `(0,1)`
  (rescale identity on `Icc 0 1`), while `hODE` is needed on `Ico 0 b` — use the
  ε-shift (start the Grönwall at `ε` with ICs from continuity) or strengthen
  the rescale lemma (blueprint note in `B0NormalCoordBounds.md`).
- then (d): the manifold IFT at `v ≠ 0` to convert `mfderiv` injectivity into
  `IsLocalDiffeomorphOn` (B2's `hloc`).

For the volume-comparison V1c lane, the next smallest theorem is the radial
instantiation of `covGronwall_bounds`.  The exact missing API is still the
regularity/ODE-bound package for `radialJacobiField` on `Icc 0 b`: parallel
frame hypotheses, `chartRepAt` differentiability for `J` and `D_tJ`, the
curvature-norm bound on `Ico 0 b`, and the `t = 0` endpoint of the Jacobi ODE.

## Lean gotchas

- `HasFDerivAt.comp_hasDerivAt` has the base point `x` as an EXPLICIT argument
  (section variable) — `hl.comp_hasDerivAt t hf`.
- `hasDerivAt_pi.mpr` needs the Pi-valued function pinned by an expected type
  (higher-order unification).
- `set`-bound `Y` crossings handled by `show` (zeta-defeq), avoiding the
  β-unreduced `rw [hYdef]` trap; `PiLp.ext` for EuclideanSpace equalities;
  `(EuclideanSpace.equiv ι ℝ).symm c i = c i` is `rfl`.
- Stale-olean shape: a just-added upstream lemma (`gronwall_ne_zero`) reported
  "Unknown identifier" until the upstream module was target-built.

## 2026-07-08 localized curve-regularity interface

Added pointwise-regularity variants `covGronwall_bounds_at` and
`covGronwall_ne_zero_at`.  They replace the old global
`ContMDiff ... γ` input with
`∀ t ∈ Icc 0 b, ContMDiffAt ... γ t`, which is exactly what the Gronwall proof
uses for the two metric-compatibility differentiations.  The old
`covGronwall_bounds` and `covGronwall_ne_zero` names are preserved as
compatibility wrappers.

Verification passed.  A downstream stale-import failure in `RadialGronwall`
was resolved by refreshing this module after the focused check passed.  The
remaining project blocker is above this layer: the endpoint/finite/density
radial-Jacobi consumers still have global-regularity wrappers until the `_at`
interface is threaded upward.
