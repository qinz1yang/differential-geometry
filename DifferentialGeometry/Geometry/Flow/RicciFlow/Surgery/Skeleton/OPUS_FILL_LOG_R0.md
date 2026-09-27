# OPUS fill log — brick R0 (round spatial component has definite volume)

Date: 2026-09-26. Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`.
Route: the H4 digest cover route (Killing–Hopf cover + `diffeomorphSc`); §6.4 exp route not built.
R0b delivered as the explicit LOWER BOUND (not the exact `12√6π²`); R1 constant is therefore `4√3π`.

## Files (new, unregistered in `DifferentialGeometry.lean` — lead registers)

| File | Lines | Content |
|---|---|---|
| `Geometry/Metric/Sphere/Quotient/SimplyConnectedSpaceForm.lean` | 68 | general R0a |
| `Geometry/Metric/Sphere/Round/BallVolumeBound.lean` | 320 | `vol S^n ≥ vol B^n`, `vol S³ ≥ 4π/3` |
| `Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/SpatialRoundComponentVolume.lean` | 169 | R0a, R0b, R0 specialised; R1 |

## Existing file touched (one-line visibility change)

`Analysis/Integration/Measure/Riemannian/MetricComparison.lean`: `private lemma det_le_of_quad_le`
→ `lemma det_le_of_quad_le` (full name `DifferentialGeometry.Integral.Measure.det_le_of_quad_le`,
unique library-wide). Needed for `det (gram b) ≤ det (gram (L ∘ b))` when `‖u‖ ≤ ‖L u‖`.
The lead may want a better public name (e.g. `det_le_det_of_quadratic_le`); only the use site in the
same file and `BallVolumeBound.lean` would change.

## Public declarations

- `DifferentialGeometry.Geometry.exists_isometry_round_sphere_of_constant_positive_sectional_curvature`
  (general `n`, `c`: `[CompactSpace M] [SimplyConnectedSpace M] [I.Boundaryless]`, `1 < n`,
  `finrank E = n`, sectional identity in the `metricRm04StandardAt` convention ⇒
  `∃ Φ : M ≃ₘ⟮I, 𝓡 n⟯ S^n, roundMetric (Φ x) (dΦ v) (dΦ w) = c * g x v w`).
- `DifferentialGeometry.Geometry.ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ`
  (`[NeZero n]`: `ofReal (√π^n / Γ(n/2+1)) ≤ vol_round(S^n)`), and
  `ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ` (`n = 3`).
- Namespace `…Perelman.CanonicalNeighborhood.FiniteHorn`:
  - R0a `exists_isometry_roundSphereThree_of_constantCurvature` — statement verbatim from §6.3.
  - R0b `ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_roundSphereThree_univ`:
    `ofReal (8 * √6 * π) ≤ vol(RoundSphereThree, roundSphereThreeMetric) univ`.
  - R0 `ofReal_eight_sqrt_six_mul_pi_le_riemannianVolumeMeasure_univ_of_constantCurvature`:
    same hypotheses as §6.3 R0, conclusion `ofReal (8 * √6 * π) ≤ vol_h univ`.
  - R1 `SpatialRoundComponent.volume_lower_of_simplyConnected`: §6.3 statement with the constant
    `4 * Real.sqrt 3 * Real.pi` in place of `6 * Real.sqrt 3 * Real.pi ^ 2`.

## Statement changes vs §6.3 and why

- R0b/R0/R1: bound instead of exact value (explicitly allowed by the brief/digest). Exact `2π²` would
  need the polar integral of `(1−|y|²)^{-1/2}` over `B³`, the equator null set and both hemispheres;
  the bound needs only one graph chart with density `≥ √det(Gram)` (projection trick `P ∘ Ψ = id`,
  `‖P‖ ≤ 1`, so `‖u‖ ≤ ‖dΨ u‖`). Hence names say `ofReal_eight_sqrt_six_mul_pi_le_…` instead of
  `…_univ` / `…_univ_of_…` equalities. R1 keeps its §6.3 name; constant `6√3π²` → `4√3π`.
- The `n`-sphere bound needs `[NeZero n]` (Mathlib's `InnerProductSpace.volume_ball` needs a
  nontrivial space).
- R0a specialisation lives in the flow file, not next to `PositiveSpaceForm.lean`, because
  `RoundSphereThree`/`roundSphereThreeMetric`/`I3` are defined under `Perelman/CanonicalNeighborhood/`;
  the general theorem is in `Geometry/Metric/Sphere/Quotient/`.

## Proof notes

- R0a: cover theorem (`n = 3`, `c = 1/6`), `LocallyPathConnectedSpace` via `I.toHomeomorph`
  + `ChartedSpace.locallyPathConnectedSpace`, sphere connected via `isConnected_sphere`,
  `Φ := (hcovering.diffeomorphSc hlocal).symm`, chain rule on `cover ∘ Φ = id`; `roundSphereThreeMetric`
  is `scaleMetric 6 roundMetric`, so `6 * (1/6) h = h`.
- R0: `riemannianVolumeMeasure_image_sandwich` (VolumeTransport) with `F = Φ.toPartialDiffeomorph`,
  `a = b = 1`.
- R1: `SimplyConnectedSpace D.Z` from the homeomorphism `Z ≃ₜ U` built from `D.map`
  (`source_eq`, `target_eq`, `toHomeomorphSourceTarget`); sandwich with `a = 2Q`, `b = 2/Q` from
  `metric_bounds`; `√((2Q)³) = 2√2·Q√Q`, `8√6 = 2√2·4√3`.

## Compile status

All three files compile with `lake env lean` (2 threads, lakefile `leanOptions` passed:
`maxSynthPendingDepth=3`, `weak.linter.mathlibStandardSet=true`): 0 errors, 0 warnings, 0 infos.
`#lint` on scratch copies: 0 errors (14 linters) for each file.
Because `det_le_of_quad_le` changed visibility, the shared `.lake/build` olean of
`MetricComparison` is stale; verification used a scratch LEAN_PATH mirror
(`C:\Users\liao9\AppData\Local\Temp\claude\r0\mirror`, junctions + recompiled MetricComparison and
the new modules). `.lake/build` was not written. `lake build` must rebuild `MetricComparison` and
its dependents.

## Axioms (via `#print axioms`, then removed)

`SpatialRoundComponent.volume_lower_of_simplyConnected`: `[propext, Classical.choice, Quot.sound]`.
Same for R0a, R0 and the two general theorems. No `sorryAx`.
