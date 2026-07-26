# SegmentArea.lean — L5, the manifold non-injective area inequality

Deliverable **L5** of the A0′ `VolumeComparisonInput` lane (brick B5c).  This is the
"missing bridge" the B2 lane flagged as its frontier: a non-injective
change-of-variables **inequality** for `expMapIntrinsic x : E → M` into a Riemannian
manifold, valid past the cut locus.

## Status

- **GREEN, sorry-free, verified** (focused check + targeted build
  `+…Comparison.Volume.SegmentArea`, 3818 jobs, exit 0).  370 lines.

## Public API

- `riemVol_exp_image_le` (main L5): for `IsCompact K` (⊆ `E`),
  `riemannianVolumeMeasure g (expMapIntrinsic x '' K) ≤ ∫⁻ v in K, ofReal (expJacDensity x v) ∂modelHaar`.
  No injectivity, no cut-locus hypothesis.

## Private helpers

- `expJacDensity g hEnorm x v` := `curveDensity g (intrinsicGeodesic x v)
  (fun i t => intrinsicJacobi x v (chartModelBasis i) t) 1` — the RHS integrand, i.e.
  the pointwise Riemannian Jacobian of `exp_x` (= `exp_density_curve`'s value).
- `expJacDensity_continuous` — continuity of `v ↦ expJacDensity x v`, needed for the
  `lintegral_tsum` swap.  Proved locally from `exp_density_curve`
  (`= chartDensity · |det (chart∘exp)|`) + `chartDensity_continuousOn` +
  `ContDiffAt.continuousAt_fderiv` (via `expChart_contDiffAt`) + `continuous_det`.
- `pou_term_exp_le` — the per-chart summand bound (the crux).

## Route (verified)

`riemannianVolumeMeasure g = Measure.sum (α ↦ (chartLocalMeasure g α).withDensity
(ofReal∘ρα))`, `ρ = chartAtlasPOU`.  On compact `K` the image is measurable, so
`Measure.sum_apply` is an EQUALITY.  Each α-summand is bounded by `pou_term_exp_le`,
then the α-sum is restricted to the countable POU support
(`tsum_subtype_eq_of_support_subset` + `countable_nonempty_support_of_pou`), swapped
inside the integral (`lintegral_tsum`), and collapsed by `∑_α ρα(exp v) = 1`
(`tsum_ofReal_pou_eq_one` + `ENNReal.tsum_mul_right`) to `∫⁻ v in K, ofReal(expJacDensity v)`.

`pou_term_exp_le`: `ν_α(exp''K) = ∫⁻ p in target, ofReal(chartDensity(symm p)) ·
(exp''K).indicator(ofReal∘ρα)(symm p)` via `withDensity_apply` +
`chartLocalMeasure_setLintegral_indicator`.  The pulled-back integrand equals
`(fα''Kα).indicator Wα` on the chart target (`fα = chart∘exp` piecewise, `Kα = K ∩
exp⁻¹ source`, `Wα = ofReal(chartDensity·ρα)∘symm` piecewise), so
`≤ ∫⁻ q in fα''Kα, Wα` (`setLIntegral_congr_fun` + `setLIntegral_le_lintegral` +
`lintegral_indicator_le`), then `image_lintegral_le` (L3) gives
`≤ ∫⁻ v in Kα, Wα(fα v)·ofReal|det fα'|`, whose integrand is rewritten by
`exp_density_curve` to `ofReal(ρα(exp v))·ofReal(expJacDensity v)`; finally
`Kα ⊆ K`.

## Lean lessons (durable)

- **`ContinuousMul ℝ≥0∞` does NOT exist** (ENNReal mul is not jointly continuous at
  `0·∞`).  For a ContinuousOn product of two `ofReal`s, fold to a single
  `ofReal (a*b)` (`ENNReal.ofReal_mul`, needs `0 ≤ a`) so the real product carries the
  `ContinuousMul ℝ`.
- **Global measurability of `extChartAt ∘ f` / `weight ∘ symm`**: charts are only
  `ContinuousOn` source/target; make the map global with `Set.piecewise … 0` and prove
  `Measurable` via `ContinuousOn.measurable_piecewise` (open/measurable set + the two
  ContinuousOn branches).  `image_lintegral_le` needs the global `Measurable f`/`w`.
- **`set x := e with h` makes `x` opaque** (not delta-reducible in unification), so
  `Set.piecewise_eq_of_mem` (which needs to see `s.piecewise f g i`) fails on `fα v`.
  `rw [h]` first, or factor a reusable `hpw : ∀ w ∈ Uα, fα w = chart(f w)` helper.
- `Set.piecewise_eq_of_mem` takes **explicit `s f g`** then the membership:
  `Set.piecewise_eq_of_mem _ _ _ hmem`.  Dot notation `Uα.piecewise_eq_of_mem` mis-binds.
- **`obtain ⟨…⟩ := hpimg` consumes `hpimg`** — reconstruct the membership
  (`⟨v, hvKα, hvp⟩`) if you need it again downstream.
- Non-measurable image handling: `∫⁻ y in f''s, w ∂μ` (setLIntegral over a possibly
  non-measurable image) is fine for the outer measure; only the manifold-side
  `Measure.sum_apply` needs `exp''K` measurable, obtained from `IsCompact K`.
- restrict ≤ full: `setLIntegral_le_lintegral`; indicator ≤ set-integral:
  `lintegral_indicator_le`; both unconditional (no measurability of the set).
- POU continuity accessor: `(chartAtlasPOU I M α).contMDiff.continuous`.
- `ContDiffAt.continuousAt_fderiv (h) (hn : n ≠ 0)` gives ContinuousAt of `fderiv`.

## Downstream (B5c L6/L7)

Consumers: `SegmentPolar.segBall_vol_le` should apply `riemVol_exp_image_le` with
`K = SegDom ∩ closedGBall R` (compact), then bound `∫⁻_K expJacDensity ≤ σ·hypRadVol`
via the Gauss radial/transverse split + Euclidean polar (`lintegral_polar`).  That
absolute-bound step is L6 and is NOT in this file.
