# A0′ area-inequality frontier — GPT-Pro consult (revised draft)

Status: REVISED 2026-07-25 after the B5-pre read-only scout (findings: plan
§8 "B5-pre scout findings") corrected two premises of the first draft and
narrowed the frontier.  Submission still BLOCKED on browser access (no
Chrome extension connected; per CLAUDE.md the in-app browser login state is
not assumed sufficient).  Submit via the CLAUDE.md Pro-consult protocol
("Lean Pro Consult Handoff" ChatGPT project, fresh chat).  Evidence mode:
local changes are NOT pushed — attach the files listed at the bottom instead
of presenting the GitHub branch as current.

Division of labor already decided (do not re-ask Pro about these): the
measure scaffolding L3 (weighted non-injective Euclidean area `≤`, from
Mathlib `Jacobian.lean:903` by simple-function approximation) and L4
(per-chart `≤`-decomposition of `riemannianVolumeMeasure`, near-definitional
since the measure is a POU-weighted sum of chart-local measures) are being
implemented as brick B5a.  The consult targets ONLY the coupled frontier
L1(large-v) + L2 below.

---

## Prompt to send

I am working in a large Lean 4/mathlib project. Do not write code first. Diagnose the proof obstruction and give a small lemma frontier.

Target theorem:
Two `sorry`-stated theorems in `DifferentialGeometry/Geometry/Comparison/Volume/SegmentPolar.lean` (file attached), for a complete connected Riemannian member `(M, g)` modeled on a finite-dimensional inner-product space `E` (`n := Module.finrank ℝ E`, `NeZero n`), with `hEnorm : ∀ y w, ‖w‖ₑ = ENNReal.ofReal (√(g.inner y w w))`:

- `segBall_vol_rel` (capped relative Bishop–Gromov, division-free): for `0 ≤ q`, `0 < s ≤ R`, `RicciBoundedBelow g (-((n-1)·q²))`:
  `V(x,R) * ofReal (hypRadVol q (n-1) s) ≤ ofReal (hypRadVol q (n-1) R) * V(x,s)`
  where `V(x,t) := riemannianVolumeMeasure g {y | riemannianEDist I x y < ofReal t}`.
- `segBall_vol_le` (absolute upper bound): same hypotheses plus `0 < R`, conclusion
  `V(x,R) ≤ ((modelHaar (E := E)).toSphere Set.univ) * ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R)`
  (sphere-mass constant `σ = finrank · vol(unit ball)` is essential; flat ℝ² is the equality case). A corollary `segBall_vol_fin` (`V(x,R) < ⊤`) is already proved from it.

The route (validated in-repo; measure side already underway) is Bishop–Gromov past the cut locus over the segment domain:
`SegDom g hEnorm x := {v | √(g.inner x v v) = (riemannianEDist I x (expMapIntrinsic g hEnorm x v)).toReal}` with (all PROVED, sorry-free): star-shapedness `segDom_smul`, Hopf–Rinow covering `ball_sub_image_segDom` (the edist-ball ⊆ `expMapIntrinsic '' (SegDom ∩ gBall)`, non-injective), `isClosed_segDom`/measurability; no-conjugacy of interior points of minimizing segments (`tail_no_conj`); the intrinsic Bishop density comparison ((β): `exists_intrRatio` — AntitoneOn of `curveDensity/hypDensity` on conjugate-free windows under the Ricci bound; `intrDens_le_hyp` — pointwise `curveDensity ≤ N·hypDensity`); a truncated cross-Chebyshev integral lemma ((γ): `lintegral_cross_le`, `crossAnti_ofReal`, `crossAnti_indicator`); and the measure decomposition: `riemannianVolumeMeasure` is BY CONSTRUCTION a partition-of-unity-weighted sum of chart-local measures `chartLocalMeasure g α = Measure.map (extChartAt I α).symm ((modelHaar.restrict …).withDensity (ofReal ∘ chartDensity g α))`, so `V(S) ≤ ∑'_α chartLocalMeasure g α S` is near-definitional, and Mathlib's `addHaar_image_le_lintegral_abs_det_fderiv` (`Jacobian.lean:903`; `E → E`, MeasurableSet s + pointwise `HasFDerivWithinAt` on s, NO injectivity) does each Euclidean piece; its weighted variant is a routine helper being built.

Current goal (the ONLY remaining genuine frontier — everything else above is proved or routine assembly):
The coupled pair feeding the `E → M` non-injective area inequality
`riemannianVolumeMeasure g (expMapIntrinsic x '' A) ≤ ∫⁻ v in A, ofReal (radial Jacobi density at v) ∂modelHaar` (A = SegDom ∩ ball, measurable, star-shaped, conjugate-free interior):

- **L1 (large-v regularity):** differentiability (C¹, or the weakest thing the area argument needs — even mere pointwise `HasFDerivWithinAt` a.e. on A) of `v ↦ expMapIntrinsic g hEnorm x v` at `v ≠ 0` BEYOND the small ball where `expMapIntrinsic = expMap` holds. In-tree reality (verified by grep, statements read): at `v = 0` there is `mfderiv_expMapIntrinsic_at_zero` (= id); on a SMALL ball there is `exists_expMapIntrinsic_eq_expMap_radius` (∃ ρ > 0 agreement with the chart-fixed `expMap`) and the chart-fixed small-ball family `expMap_contMDiffAt_of_norm_lt` (gated `‖w‖ < δ` — there is NO arbitrary-`v≠0` lemma; a previously cited `expMap_contMDiffAt_of_ne_zero` DOES NOT EXIST); and there is a variational lemma `expMapIntrinsic_variation_contMDiff` for the map `(s,t) ↦ expMapIntrinsic (γ t) (s • V₀ t)` with heavy chart-flow hypotheses — it does NOT specialize to joint smoothness in the velocity. For large `v` the geodesic crosses several charts, so this is smooth dependence on initial conditions ACROSS charts for the time-1 geodesic flow. `expMap` (chart-local def via `maximalGeodesic`, junk value off the maximal interval) equals `expMapIntrinsic` only locally; global equality is not available.
- **L2 (density identity, riskiest):** identify the velocity-differential with the radial Jacobi fields to get, past the cut locus on conjugate-free directions, `|det D(extChart_α ∘ expMapIntrinsic x)_v| · chartDensity_α (expMapIntrinsic x v) = curveDensity (radial Jacobi frame at v)` — the diffeo-regime template is `normalDensity_curve` (`RadialGram.lean:470`, proved for `paramDensity (expMapDiffeo)` = `normalChartDensity` inside the normal chart), but nothing exists past the chart scale.

Exact error:
None — missing-API/design consult. The two `sorry`s elaborate; the frontier is the absent L1/L2 layer.

What was tried:
1. Direct `measure_image_le`-style CoV for the manifold target — no such lemma anywhere; Mathlib's Jacobian layer is `E → E` Haar-target.
2. In-tree change of variables (`riemannianVolumeMeasure_image_param_eq`, `normalBall_polar`, `framedBall_polar`) — all take a `PartialDiffeomorph`, i.e. diffeomorphism-only; fails exactly past the cut locus.
3. Alternative decompositions (read-only scout, 4 parallel sub-inventories): (a) "open strictly-minimizing star + diffeo CoV + null cut locus" — circular (the null-cut-locus fact is itself a C¹-image-of-null `E → M` statement) and the open-star `PartialDiffeomorph` (openness + InjOn + C¹ inverse) has no in-tree support; (b) direct per-direction polar Fubini — the polar kit exists (`toSphere`, `volumeIoiPow`, in-tree `normalBall_polar`) but only whole-ball diffeo-only, and the covering `ball ⊆ exp '' (SegDom ∩ gBall)` is non-injective, so the multiplicity-absorbing `E → M` `≤` is needed anyway. Chart-partition is the shortest route; only L1+L2 are genuinely open.

Constraints:
- Preserve public APIs; small helper lemmas; canonical homes (regularity under `Exponential/Smoothness/`, density identity near `Comparison/Volume/RadialGram`); no new axioms; no broad refactors; no blind automation.
- Members are σ-compact, T2, complete, connected — NOT compact; no injectivity-radius input allowed (the whole point of the lane).
- L3/L4/L5 (weighted Euclidean area helper, per-chart decomposition, final `E → M` assembly) are underway separately — do NOT spend the answer on them.
- An honest partial is acceptable: the two `sorry`s may stay while the L1/L2 layer is built first.

Tasks:
1. For L1: what is the cleanest Lean-4 route to velocity-differentiability of the intrinsic exponential past chart boundaries? Candidates we see: (a) compose chart-local geodesic-flow smoothness along a finite chart chain covering the compact segment `t ↦ expMapIntrinsic x (t•v₀)`, `t ∈ [0,1]` (the tree has chart-local ODE/flow infrastructure under `Exponential/Smoothness/` and `ExpVariationSmooth`; what exact statement should the chain-composition lemma have, and is C¹ in `v` obtainable by iterating "C¹ in (point, velocity) of the chart-local time-`t` flow"?); (b) geodesic flow as the flow of a smooth spray on the tangent bundle — does Mathlib (or a standard pattern) give ContMDiff of the time-1 flow map of a smooth vector field on a manifold, applicable to `TM`?; (c) something slicker we're missing. Give the smallest lemma chain with statements.
2. For L2: can the determinant identity be obtained WITHOUT a standalone global L1 differential — e.g. by propagating the Jacobi-Gram determinant through chart transitions along the geodesic (each chart window reuses the proved diffeo-regime `normalDensity_curve`-style identity; transitions contribute cocycle `|det|` factors), so that only PIECEWISE chart-local regularity is ever used? Or is the honest route "L1 first, then differential-of-exp = Jacobi field by variation of initial conditions"? Judge which is shorter in Lean.
3. Risk-rank L1(a)/(b)/(c) and L2-piecewise vs L2-via-L1; give the implementation order, the first brick to dispatch, and the failure signals that should trigger a re-consult.
4. Sanity check: any existing Mathlib development (recent additions included) on manifold area/coarea formulas, images of null sets under C¹ manifold maps, or exponential-map regularity that we should reuse instead of building?

Files attached: `SegmentPolar.lean` (frontier statements + header documenting the obstruction), `SegmentDomain.lean` (proved covering layer), excerpts: `exists_intrRatio`/`intrDens_le_hyp` (BishopIntrinsic.lean/IntrinsicRatio.lean), `lintegral_cross_le` (RatioIntegral.lean), `normalDensity_curve` statement (RadialGram.lean:470), `mfderiv_expMapIntrinsic_at_zero`, `exists_expMapIntrinsic_eq_expMap_radius`, `expMapIntrinsic_variation_contMDiff` signature (ExpVariationSmooth.lean:829ff), plus the "B5-pre scout findings" block of `A0PRIME_VOLUME_PLAN.md` §8 (full in-tree inventory with file:line references).

---

## Answer (paste back after the consult)

(pending)
