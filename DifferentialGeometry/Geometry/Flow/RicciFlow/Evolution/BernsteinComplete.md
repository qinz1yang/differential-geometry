# BernsteinComplete

The July 22 sections below are chronological checkpoints and are superseded by
the July 23 fixed-order capstone and accounting at the end of this note.

## 2026-07-22 architecture correction

`BernsteinTower.estimate_complete` must not be proved under its current
signature.  Uniform metric equivalence and an evolving-metric Ricci lower
bound do not control the evolving Laplacian of an anchor-distance cutoff, and
an arbitrary scalar subsolution has no growth-free complete-noncompact maximum
principle.  The declaration remains temporarily because `MovingShiOpen` still
calls it, but its docstring now marks it as a legacy unsupported frontier.

Added the canonical consumer predicate `TowerNormGradOn`.  It retains the
geometric estimate

`|∇w_k|² ≤ 4 w_k w_(k+1)`

needed to absorb cutoff-gradient terms against the negative next-level tower
term.  The actual curvature-tower producer is `towerNorm_grad_le` in
`IteratedRmTowerHeatEq.lean`.  Focused verification passed; the only warning is
the pre-existing legacy `sorry`.

## Exact frontier

The replacement chain still needs:

1. generated quantitative parabolic cutoff data for a complete
   bounded-curvature Ricci flow;
2. a localized Bernstein induction that retains the negative `w_(i+1)` terms;
3. migration of `MovingShiOpen.complete_of_heat` away from the current
   truncated tower, whose zeroed `m+1` level cannot satisfy the Kato estimate
   needed at the top level.

This is a substantive analytic/localization frontier, not a coercion issue and
not an HCG input gap.

## Accounting

- corrected complete-noncompact estimate: theorem-level 0%;
- `TowerNormGradOn` and the curvature Kato producer: complete;
- dedicated complete-Bernstein machinery: roughly 30--35%;
- end-to-end complete arbitrary-dimensional Shi producer: theorem-level 0%;
- unconditional `compactnessSol`: theorem-level 0%.

## 2026-07-22 localization algebra

`ShiCutoffData` now records one compact spatial support for each cutoff over
the whole time slab.  Its parabolic field has the sign required by
`P = ∂ₜ - Δ`: the localized product identity contains `G * Pχ`, so the
consumer needs `Pχ ≤ err`, recorded as `parabolic_le`.  The former lower bound
`-err ≤ Pχ` had the wrong direction for an upper Bernstein estimate and had
no consumers.

The checked `ShiCutoffData.cross_le` combines the cutoff gradient bound,
`TowerNormGradUpTo`, metric Cauchy--Schwarz, and scalar Young inequality to
prove

`-2 <∇χ,∇w_k> ≤ χ w_(k+1) + 4 err w_k`.

The direct projections `space_diff` and `grad_diff` expose the spatial
regularity already contained in `space_smooth` for the parabolic product
rule.  Focused verification passed; the remaining warning is the pre-existing
legacy `estimate_complete` proof frontier.

## 2026-07-22 graded localization correction

The tempting common-factor polynomial `chi * Gfun` does not close.  The
levelwise cross estimate produces the full weighted next-level sum, whereas
`Gfun_dissipative` retains only the top term; the difference has no sign.  Even
retaining the whole sum would leave an uncontrolled `err * Gfun` leakage on a
noncompact manifold.

The canonical replacement is `GfunCut`, with level `i` weighted by
`chi^(i+1)`.  `GfunCut_zero` and `GfunCut_one` record compact support and exact
agreement on the exhausted region; `GfunCut_nonneg` records its sign on the
controlled slab.  This graded weighting lets each cutoff
error be charged to the previous tower coefficient; only the level-zero error
remains, where `w 0 <= K^2` controls it.

Two routine API seams precede the localized induction: natural-power gradient
and parabolic formulas, and the compact-support weak maximum principle with a
nonnegative (rather than identically zero) exterior barrier.  The latter is
now supplied by `strict_barrier_cpt`.  The remaining graded algebra is
substantial but local; the genuinely independent analytic blocker after it is
the solution producer for `ShiCutoffData`.

Accounting remains honest: the corrected complete-Bernstein theorem is 0%;
its dedicated localization machinery is about 45%.  The trusted complete Shi
producer and unconditional HCG endpoint remain theorem-level 0%.

## 2026-07-22 graded cutoff powers

The two natural-power estimates required by the graded recurrence are now
checked:

- `ShiCutoffData.pow_parabolic_le` proves
  `P(chi^(p+1)) <= (p+1) * err * chi^p` without assuming `chi > 0`;
- `ShiCutoffData.pow_cross_le` spends half of the next tower level and leaves
  `8 * (p+1)^2 * err * chi^p * w_k`.

The first uses the canonical zero-safe `gradientFun_pow` theorem and an
induction through `parabolic_mul`.  The second uses metric Cauchy--Schwarz and
Young's inequality directly, so the exact coefficient needed by the finite
recurrence remains visible.  `GfunCut_off` and `GfunCut_cont` now also provide
the compact exterior and joint-continuity facts needed by the weak maximum
principle.  Focused verification passed; the only remaining warning is the
deliberately visible legacy `estimate_complete` `sorry`.

These bricks do not prove the corrected complete-Bernstein theorem, which is
still theorem-level 0%.  Its dedicated localization machinery is now about
55%; the next local target is the finite-sum `GfunCut` parabolic recurrence.
The independent solution-produced quantitative cutoff family remains the
later genuine analytic blocker.

## 2026-07-22 graded finite recurrence

The localized finite-tower algebra is now checked.  The private telescope
absorbs every positive-level cutoff error into the previous retained
next-level term under

`2 * cut.err n * B.T * cutErrCoeff m <= 1`.

The public theorem `GfunCut_parabolic_le` combines that telescope with the
per-level parabolic product rule, the retained-good and top reaction estimates,
and finite-sum linearity.  Its conclusion is

`P(GfunCut) <= textbookForce * K^3
  + 9 * cut.err n * Gcoef m 0 * K^2`.

The coefficient `9` is `cutErrCoeff 0`; the remaining base error is bounded by
the existing curvature hypothesis `w 0 <= K^2`.  Time, spatial, and gradient
regularity for the finite summands are assembled locally from `BernsteinTower`,
`ShiCutoffData`, and `ScalarWeak.parabolic_sum`; no parallel public regularity
API was introduced.  Focused verification passed.  The only warning is the
pre-existing legacy `estimate_complete` `sorry`.

Honest accounting:

- `GfunCut_parabolic_le`: theorem-level 100%;
- corrected complete-noncompact estimate: theorem-level 0% (the public
  replacement capstone is not yet stated and proved);
- dedicated complete-Bernstein localization machinery: roughly 70%;
- generated `ShiCutoffData` for the solution: theorem-level 0% and still the
  independent analytic producer frontier;
- end-to-end complete arbitrary-dimensional Shi and unconditional
  `compactnessSol`: theorem-level 0%.

## 2026-07-23 fixed-order cutoff capstone

The canonical public consumer is now
`BernsteinTower.estimate_cutoff_at`.  At a requested order `m`, it uses only
`TowerNormGradUpTo B m`; the previous all-order
`BernsteinTower.estimate_of_cutoff` remains as a compatibility wrapper obtained
from `hgrad.upTo m`.  No proof body or constant recurrence is duplicated.

The proof keeps the cutoff index internal.  Strong induction supplies the
lower tower levels together with the corresponding restriction of the finite
Kato prefix.  For every sufficiently small cutoff error it applies
`strict_barrier_cpt` to the graded polynomial on the cutoff's uniform compact
support.  At the requested spacetime point, `exhausts` identifies the graded
polynomial with the ordinary Bernstein polynomial.  Finally `err_tendsto`
removes the remaining level-zero error, and the existing textbook constant
recurrence gives exactly

`t^m * w m t x <= (towerConst c alpha m)^2 * K^2`.

Focused verification and the exact target refresh are GREEN (`3738/3738`).
The only warning is the deliberately retained legacy `estimate_complete`
`sorry`; the fixed-order capstone and compatibility wrapper are sorry-free.

Honest accounting after this brick:

- `BernsteinTower.estimate_cutoff_at`: theorem-level 100%, focused/exact-current;
- `BernsteinTower.estimate_of_cutoff`: theorem-level 100%;
- corrected complete-noncompact Bernstein consumer: theorem-level 100%;
- dedicated localization machinery and capstone: 100%;
- solution-generated quantitative `ShiCutoffData`: theorem-level 0%, now the
  single independent analytic blocker for the complete Shi route;
- end-to-end complete arbitrary-dimensional Shi: theorem-level 0%;
- unconditional `compactnessSol`: theorem-level 0%.

## 2026-07-23 Route B-prime data extraction

The unchanged smooth `ShiCutoffData` definition and its three route-neutral
helpers now live in `Evolution/ShiCutoffData.lean`.  `BernsteinComplete` imports
that module; its existing smooth fixed-order theorem and compatibility wrapper
continue to focused-check unchanged.  The extracted module and
`BernsteinComplete` both passed exact targeted verification; the only warning
remains the documented legacy `estimate_complete` `sorry`.

The new data module also owns the local lower-support and point-centered
barrier-cutoff interfaces.  At the time of extraction no barrier recurrence
was hidden there; the later quantifier-corrected consumer is recorded below.
The exact-current smooth `BernsteinTower.estimate_cutoff_at` remains
theorem-level 100%.

The extraction itself advanced the selected Route B-prime machinery to roughly
15--20%; see the later section for the current consumer status.

## 2026-07-23 barrier-consumer quantifier correction

The first attempt to implement the consultation's displayed
`estimate_barrier_at` signature exposed a genuine quantifier defect.  At a
negative minimum the compact-support maximum principle selects an arbitrary
point `y`.  The graded reaction estimate there needs every strict lower-order
bound at `y`.  A single
`ShiBarrierCutoffData G T O` only exhausts its fixed center `O`, so strong
induction from that input supplies lower-order estimates at `O`, not at the
selected `y`.  This is exactly where the smooth proof used its global
`exhausts` field.

The canonical repair is to consume a point-centered cutoff family

```lean
hcut : ∀ y, Nonempty (ShiBarrierCutoffData (I := I) G B.T y)
```

and conclude the estimate at every point.  This is the data already produced
by the intended solution-level caller, which constructs a distance cutoff
after the requested point is known.  It adds no geometric hypothesis and does
not restore global exhaustion.

The local analytic refactor is complete in source:

- `supportLevel_le` consumes one `ShiCutoffLowerSupportAt`;
- `GfunSupport_parabolic_le` supplies the local regularity and unchanged
  graded recurrence for its lower support;
- the old smooth `cutLevel_le`, `GfunCut_parabolic_le`, and
  `estimate_cutoff_at` remain compatibility consumers;
- the revised `estimate_barrier_at` selects the cutoff centered at the final
  point, builds an affine-minus-local-polynomial upper support at every
  possible negative minimum, applies
  `strict_barrier_cpt_of_upperSupport`, and then uses `center_exhausts` and
  `err_tendsto`.

The source proof contains no new placeholder; focused verification is GREEN,
and the exact targeted refresh is GREEN (`3749/3749`).  The only warning is the
pre-existing legacy `estimate_complete` `sorry`.

Honest accounting at this checkpoint:

- revised `estimate_barrier_at`: theorem-level 100%, focused- and exact-green;
- its lower-support recurrence: theorem-level 100%, focused- and exact-green;
- dedicated barrier-consumer machinery: 100%;
- solution-generated `ShiBarrierCutoffData`: theorem-level 0%;
- end-to-end complete arbitrary-dimensional Shi: theorem-level 0%;
- unconditional `compactnessSol`: theorem-level 0%;
- whole-project HCG supporting machinery remains roughly 60%.
