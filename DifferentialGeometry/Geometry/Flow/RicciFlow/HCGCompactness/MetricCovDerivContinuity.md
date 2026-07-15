# MetricCovDerivContinuity.lean — continuity + compact bounds for the HCG derivative norms

## What this file provides (P4 Brick 4 unblocker)

For FIXED smooth metrics (no time family, no solution structure):

- `metricCovDerivNorm_cont a h gRef` : `z ↦ |∇_{gRef}^a h|_{gRef}(z)` is continuous.
- `metricDerivNorm_cont a gk gInf gRef` : `z ↦ |∇_{gRef}^a (gk − gInf)|_{gRef}(z)` is continuous.
- `metricCovDerivNorm_bddOn hK a h gRef : ∃ C, ∀ z ∈ K, … ≤ C` (K compact).
- `metricDerivNorm_bddOn hK p gk gInf gRef : ∃ C, 0 ≤ C ∧ ∀ a ≤ p, ∀ z ∈ K, … ≤ C`.

This discharges the WALL recorded in `ConvFieldAssembly.md` ("NO
`metricCovDerivNorm` spatial-continuity / BddAbove API exists"): the
HEAD/MID-range of the raw `hbdd` hypothesis of `windowGInfAll` for the
bump-extended sequence `gSeqExt` is, per fixed `(k, t)` (note `windowGInfAll`'s
`hbdd` fixes `t` BEFORE `∃ C`, so no `t`-uniformity is needed), a bound on the
covariant norms of ONE fixed smooth metric over a compact — exactly
`metricCovDerivNorm_bddOn`.  Max over the finitely many head/mid `k` finishes.

## Route

`metricCovDeriv h gRef a` is BY TYPE a `Tensor0SField ∞ (a+2)` (a bundled
smooth section, `PointedConvergence.lean:80`), and
`metricDiffCovDerivAt a gk gInf gRef` is pointwise the coercion of the section
DIFFERENCE `metricCovDeriv gk gRef a - metricCovDeriv gInf gRef a`
(`ContMDiffSection` has `Sub`; the identification is definitional — `congr 1`
closes it under `backward.isDefEq.respectTransparency false`).  So both norms
are `Real.sqrt ∘ (normSq0S of a smooth field)`, and the new
`Tensor0SBundle.normSq0S_cont` (`Tensor/RSTensor/FiberMetric/
Tensor0SMetricContinuity.lean`) gives continuity.  Compact bounds via
`IsCompact.exists_isMaxOn` (NOT `exists_forall_ge` — renamed), empty-`K` case
split, and `Finset.sup'` over orders `a ≤ p`.

## What this does NOT solve (remaining Brick-4 frontiers, for the ConvFieldAssembly owner)

- `hgLip`'s MID-RANGE (bump collar): the time-Lipschitz bound for
  `χ·(g_k(s) − g_k(t))` needs `|∇^a(χ·T)| ≤ Σ binom |∇^i χ||∇^{a-i}T|`
  (a scalar-Leibniz tower for `covDerivOfField`) — continuity does NOT give the
  `|s−t|` factor.  Only the constant-`R` head (`metricDerivNorm a R R = 0`) and
  the tail (χ ≡ 1 locality + transported flow bounds) are free of it.
- The k-UNIFORM tail bounds themselves (they must come from carried
  cited-input hypotheses at source-flow granularity, or from running the
  Lemma-3.11 engine on a sequence of flows restricted to a FIXED open
  `V ⊆ L.M` — the producers need one fixed manifold).

## Verification

GREEN: focused checks + targeted build
`+DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity`
(3803 jobs, 0 errors); style warnings (`show`→`change`) cleaned.
`#print axioms` on all 4 endpoints (and the 3 Tensor-layer lemmas) =
`[propext, Classical.choice, Quot.sound]`.
## 2026-07-09: finite initial segment absorption

Added checked theorem `cov_bdd_of_eventual`: an eventual sequence-uniform covariant-derivative
bound on a compact set extends to the whole sequence because every fixed metric pair is bounded
there and only finitely many initial indices remain. This is the generic compactness bridge used
by Step D's fixed-stage pullback sequence. Focused verification and the targeted module build
passed.
