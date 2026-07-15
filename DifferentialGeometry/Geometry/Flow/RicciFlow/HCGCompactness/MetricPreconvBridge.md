# MetricPreconvBridge.lean — P3 Brick C-II (SCAFFOLD MODE)

**Status (2026-06-12): IMPLEMENTED + verified — focused check + targeted build
green (3856 jobs); `#print axioms` clean = `[propext, Classical.choice,
Quot.sound]` on all endpoints.  Brick C-II-final-A: the constants-first norm
bridge `metricDerivNorm_le_compSq_uniform` is added (good-frame witnesses bound
BEFORE `gk`/`gInf`); the old `metricDerivNorm_le_compSq` is now a thin
specialization of it.  The local-to-compact `hnorm` step is NOT attempted — it
requires higher covariant-derivative component convergence that the current
C1b output does not supply (frontier reported below).**

## C-II-final-A (2026-06-12) — constants-first norm bridge

`metricDerivNorm_le_compSq_uniform (gRef) (a) (x) : ∃ basisE u' Cu, IsOpen u' ∧
x ∈ u' ∧ u' ⊆ baseSet ∧ 1 ≤ Cu ∧ ∀ (gk gInf), ∀ z ∈ u', ∀ hz, metricDerivNorm a
gk gInf gRef z ≤ Cu · √(∑ (component0S (toBasisAt hz) (metricCovDeriv gk gRef a z)
− component0S … gInf)²)`.  The good-frame witnesses `basisE`/`u'`/`Cu` are chosen
from `exists_goodFrame_compBound gRef x` (which depends only on `gRef`, `x`) BEFORE
the `∀ gk gInf` — the P3_PLAN §5 constants-first shape required for sequence use.
The proof is the former `metricDerivNorm_le_compSq` body verbatim, with `gk gInf`
introduced inside the witness tuple (`fun gk gInf z hzu' hz => …`); `exists_goodFrame_compBound`'s
reverse bound `hrev z hz hzu' (a+2) A` is applied to `A = metricDiffCovDerivAt a
gk gInf gRef z`, valid for any `gk gInf`.  The old `metricDerivNorm_le_compSq`
(outer `gk gInf`) is kept as a 2-line specialization corollary (no Lean
consumers; only doc references).  Both axiom-clean.

## FRONTIER (C-II-final-B, the `hnorm` derivation — NOT attempted, reported per stop condition)

`metricCInfConvOnCompacts_of_normConv` consumes
`hnorm : ∀ p K compact, ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K, metricDerivNorm a
(gSeq k) gInf gRef x < ε`.  Via `metricDerivNorm_le_compSq_uniform`, producing
`hnorm` reduces to: the COMPONENT DIFFERENCES `component0S (toBasisAt)
(metricCovDeriv (gSeq k) gRef a z) − component0S … gInf` → 0, uniform on a finite
good-frame cover of `K`, for ALL `a ≤ p`.  TWO gaps block this:

- **Gap A (exposure + uniformity).**  C1b's endpoint `metricPreconv_gInf`
  (MetricPreconvDiag.lean:490) exposes ONLY order-0, POINTWISE CLM convergence:
  `∀ x, Tendsto (fun m => (gSeq (φ m)).inner x) atTop (𝓝 (gInf.inner x))`.  The AA
  engine `exists_chart_cInfConv` internally has `MapCInfConvOnCompacts` (C^∞ on
  compacts) of the ORDER-0 component chart functions, but C1b discards it.  Re-
  exposing it is C1b/MetricPreconvDiag's job (off-limits to this brick).

- **Gap B (covariant order, the real missing theorem).**  Even with the engine's
  C^∞ order-0 chart-component convergence, NOTHING turns it into convergence of
  the COVARIANT-TOWER components `component0S (metricCovDeriv (gSeq k) gRef a)` for
  `a ≥ 1`.  `metricCovDeriv g gRef a` is the a-th covariant derivative w.r.t. the
  FIXED gRef connection; its frame components are a fixed (gRef-Christoffel)
  polynomial in the coordinate derivatives ≤ a of the order-0 g components.  The
  bridge "C^∞ order-0 chart-component convergence ⇒ covariant-tower component
  convergence" — the convergence-level inverse of Brick A2's coordinate→covariant
  tower expansion — DOES NOT EXIST.  `exists_chart_cInfConv` produces
  `covDerivOfField gRef (metricTensorField (gSeq (φ k))) 0` (order 0) only; higher
  orders are in the `hbdd` HYPOTHESIS, never the conclusion.

  **Smallest next lemma to unblock**: a `componentConv_covDeriv_of_chartCInf`
  bridge — from the engine's C^∞-on-compacts order-0 chart-component convergence
  (Gap A, re-exposed by C1b) and the fixed gRef connection data, derive
  `∀ a ≤ p, component0S (metricCovDeriv (gSeq k) gRef a) → component0S
  (metricCovDeriv gInf gRef a)` uniformly on each good-frame patch.  This is a
  covariant↔coordinate component expansion at the convergence level; it belongs
  with A2/C1b, not in this C-II file.  Until it exists, the finite-cover `hnorm`
  step has no input to consume.

Scaffold mode per `P3_PLAN.md` PLANNER RULING 2: the limit metric `gInf` is a
HYPOTHESIS (its construction is the foundational brick C-G); C-II's endpoints are
parameterized by `gInf : SmoothRiemannianMetric I M` (or `ℝ → SmoothRiemannianMetric`
for the window) plus component / per-time convergence hypotheses.  When C-G + C1b
land, C1b discharges those hypotheses.

Does NOT edit `MetricPreconv.lean` or `WindowPreconv.lean` (both imported, not
touched).

## What's proved (all sorry-free, axiom-clean)

### `metricDerivNorm_le_compSq` — C2 norm bridge (local)
At a good-frame patch around `x` (the `exists_goodFrame_compBound` output,
`RicBoundGoodFrame.lean`), for any two metrics `gk, gInf`:
```
∃ basisE u' Cu, IsOpen u' ∧ x ∈ u' ∧ u' ⊆ baseSet ∧ 1 ≤ Cu ∧
  ∀ z ∈ u', ∀ hz : z ∈ baseSet,
    metricDerivNorm a gk gInf gRef z ≤
      Cu * √(∑ I0, (component0S (localFrame z) (metricCovDeriv gk gRef a z) I0
                  - component0S (localFrame z) (metricCovDeriv gInf gRef a z) I0)^2)
```
with `Cu = ((3/2)(dim E + 1))^(a+2)`.  Route: the reverse two-sided bound of
`exists_goodFrame_compBound` (`normSq0S ≤ C^s · Σ component0S²`) applied at
`s = a+2`, `A = metricDiffCovDerivAt a gk gInf gRef z`; `√(C^s·Σ) = √(C^s)·√Σ ≤
C^s·√Σ` (since `C^s ≥ 1`); and `component0S` is additive over the fibre subtraction
defining `metricDiffCovDerivAt` (the per-metric difference form — proved by `rfl`,
this is the "MetricCovDerivLinear/component-additivity" content the plan named).

This is the genuine "sup-component differences → metricDerivNorm differences"
content.  C1b applies it on a FINITE good-frame cover of a compact `K` (same
pattern as `ric_bound`) to convert per-metric frame-component convergence (the
Arzelà–Ascoli engine output) into `metricCInfConvOnCompacts_of_normConv`'s
`hnorm` input.

### `metricCInfConvOnCompacts_of_normConv` — the spatial P3 endpoint (scaffolded)
```
(hnorm : ∀ p K, IsCompact K → ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
   metricDerivNorm a (gSeq k) gInf gRef x < ε)
 → MetricCInfConvOnCompacts gSeq gInf gRef
```
The `sSup` lift: control `metricDerivNormSupOn K p (gSeq k) gInf gRef` by `ε/2 < ε`
via `metricDerivNormSupOn_le_of_forall` (WindowPreconv).  This is the
`metricPreconvInf`-shaped spatial endpoint with `gInf` supplied.

### `exists_subseq_hconv` — the dense-time diagonal wiring
```
(e : ℕ → ℝ)
(hstep : ∀ n φ, StrictMono φ → ∃ ψ, StrictMono ψ ∧
   ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
     metricDerivNorm a (gSeq ((φ∘ψ) k) (e n)) (gInf (e n)) gRef x < ε)
 → ∃ φ, StrictMono φ ∧ ∀ n, ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
     metricDerivNorm a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε
```
ONE subsequence along which spatial convergence holds at every dense time `e n`.
`hstep` is exactly the `exists_diag_subseq` (C0) refinement hypothesis; the
subsequence-stability (`hsub`, via `StrictMono.le_apply`) and tail-stability
(`hextend`, a `Nat` tail shift + `Nat.sub_add_cancel`) of the convergence property
are discharged inline; C0 does the diagonal.

### `windowPreconv_of_perTime` — the window capstone (interface check)
Composes `exists_subseq_hconv` with `windowPreconv` (Brick D, verbatim) for
`S = Set.range e`: from uniform time-Lipschitz of `gSeq`/`gInf` (`hgLip`/`hInfLip`),
a dense enumeration `e`, and the per-time refinable `hstep`, produces ONE
subsequence `φ` with window-uniform `C^p` convergence
(`metricDerivNormSupOn ... < ε`, `∀ t ∈ [β,ψ]`).  This TYPE-CHECKS my
`exists_subseq_hconv` output against `windowPreconv`'s EXACT `hconv` shape, so the
P3 assembly fits once C-G + C1b land.

## The hypothesis shapes I settled on (for the planner to validate against C-G + C1b)

1. **`metricDerivNorm_le_compSq` consumes nothing new** — it is a packaged
   consequence of `exists_goodFrame_compBound`.  Its OUTPUT is the per-patch
   inequality C1b uses; the per-metric frame-component `component0S (localFrame z)
   (metricCovDeriv g gRef a z)` is exactly what the Brick-B/AA engine converges
   (modulo the coordinate-frame ↔ trivialization-localFrame identification, which
   is C1b's responsibility — see boundary note below).

2. **`metricCInfConvOnCompacts_of_normConv` consumes** uniform-on-compacts pointwise
   `metricDerivNorm` convergence (`hnorm`).  C1b produces `hnorm` from a finite
   good-frame cover of `K` + `metricDerivNorm_le_compSq` + per-metric component
   convergence.

3. **`exists_subseq_hconv` / `windowPreconv_of_perTime` consume** the per-time
   REFINABLE spatial preconvergence `hstep` (`∀ n φ mono, ∃ ψ mono, [spatial conv
   of gSeq(φ∘ψ) at e n]`).  C1b supplies this: at each fixed time `e n`, the metric
   sequence `fun k => gSeq k (e n)` has the `(B_r)` bounds, so the per-chart AA
   extraction (`exists_chart_cInfConv`) refines any subsequence to a spatially
   convergent one — exactly the `hstep` shape.  The diagonal-over-times then comes
   for free from C0.

## Boundary left to C1b / C-G (NOT in this scaffold)
- Constructing `gInf` (the C-G inverse-componentize gate).
- The coordinate-frame ↔ trivialization-localFrame identification and the FINITE
  good-frame cover of a compact (to turn `metricDerivNorm_le_compSq` per-patch
  bounds + per-chart AA component convergence into the uniform-on-`K` `hnorm` of
  `metricCInfConvOnCompacts_of_normConv`, and the per-time `hstep`).  This is the
  same finite-cover pattern as `ric_bound`'s engine.
- The per-time `hstep` itself (the AA extraction at each dense time), which is C1b
  applied per time.

## Lean gotchas
- `component0S` of the fibre subtraction `metricDiffCovDerivAt = metricCovDeriv gk
  − metricCovDeriv gInf` splits as a difference of `component0S` by `rfl` (matches
  the WindowPreconv note: `component0S` add/sub are definitional).
- `exists_goodFrame_compBound`'s reverse bound takes args `z hz hzu' s A` with
  `hz : z ∈ baseSet` BEFORE `hzu' : z ∈ u'`.
- `hextend` (C0 `P`): `hk0 (k - m)` yields `metricDerivNorm a (gSeq ((fun k =>
  φ(k+m)) (k-m)) …)` — an UNREDUCED redex; `rw [k-m+m = k]` fails to match.  Fix:
  `simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval` (simp beta-reduces
  first, then cancels).
- `StrictMono.le_apply : k ≤ ψ k` (implicit index) for the `hsub` reindex.

## Progress (honest, nested)
- C-II scaffold: **complete + verified** (5 endpoints incl. the constants-first
  `metricDerivNorm_le_compSq_uniform`, axiom-clean).  Norm-bridge content + spatial
  endpoint + dense-time wiring + verified compose with `windowPreconv`.
- P3 (metric preconvergence → `SourceMetricCPConvOnWindow`): A1✅ A2✅ B✅ D✅
  C0✅ C-G✅ C1a/C1b✅ (`metricPreconv_gInf`, 5656ee51) C-II-final-A✅ (constants-
  first norm bridge).  REMAINING: the `hnorm` derivation (C-II-final-B) — blocked
  on Gap A (C1b re-exposing the engine's C^∞-on-compacts order-0 convergence) +
  Gap B (the covariant↔coordinate component-convergence bridge for orders a ≥ 1,
  `componentConv_covDeriv_of_chartCInf`).  Then `metricPreconvInf` assembles.
  P3 ≈ 72%.
- Lemma 3.11 / Thm 3.10 input: P1✅ P2 ~85% P3 ~72% → ≈ 63%.
- Whole HCG compactness project (MSM135 Ch3 + Ch4): ≈ 26% theorem-weighted.
