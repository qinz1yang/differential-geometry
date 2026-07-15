# MetricPreconvWindowAll.lean — Brick 3 (windowGInfAll)

## Goal
All-compacts, all-orders window preconvergence endpoint `windowGInfAll`: same raw
hypotheses shape as `windowGInf` (MetricPreconvWindowGInf.lean) but hgLip upgraded
to ∀-compacts/∀-orders, conclusion quantified over ALL compacts K and ALL orders p
with a SINGLE subsequence φ and a SINGLE limit family gInf.

## Design decision (the real content of this brick)
The naive route "diagonalize `windowGInf` per (K_j,j) and glue the per-j window
limits" FAILS: `windowGInf`'s window family `gAt t` is a `metricPreconvFull`
limit that is globally pinned (all x) only along a TIME-DEPENDENT sub-subsequence
`psiAt t`. Along the master φ it is pinned only ON the compact K (order-0
seminorm convergence). Two per-j families therefore agree only on the smaller
compact `K_min(i,j)`, never globally — so they do NOT assemble into one metric,
and even the FINAL `metricDerivNormSupOn K p ... gInf t ...` needs gInf to equal
the per-j limit on a NEIGHBORHOOD of K (covariant derivatives are local), i.e.
globally. Repeatedly re-derived; see the long reasoning — this is a genuine
obstruction, not a bookkeeping gap.

The correct level to diagonalize is the NET-TIME GLOBAL tendsto (all x), which
`netFullDiag` DOES expose (MetricPreconvWindowGInf.lean:251-253: full-φ,
all-x inner Tendsto of the net-time limits). At net times the limits are forced
UNIQUE by `tendsto_nhds_unique`, so ONE global `gNet : ℕ → SmoothRiemannianMetric`
survives the diagonal.

## What LANDED (structure, verified pieces pending build confirmation)
- `metric_ext_inner`: two `SmoothRiemannianMetric` are equal iff `.inner` agree at
  every point (structure ext + `ContMDiffRiemannianMetric.mk.injEq`; the other
  fields are Prop / determined by `inner`).
- `windowGInfPt`: `windowGInf` re-derived to ALSO expose (a) the window
  convergence in POINTWISE form (`metricDerivNorm ... < ε`, via `windowPreconv`'s
  internal three-term split done inline as `hwinPt`), and (b) the window-limit
  family's per-time all-x inner Tendsto (read off `gAt`'s `metricPreconvFull`
  output `(hgAt t ht).1`). Reuses `netFullDiag`, `metricPreconvFull`,
  `netCauchyAt`, `fullOfSubseq`, `infLipOfConv` directly (all public in
  MetricPreconvWindowGInf.lean).
- `windowGInfAll` scaffold: compact exhaustion via `CompactExhaustion.choice M`
  (needs `[WeaklyLocallyCompactSpace M]` — added as an explicit instance arg;
  manifolds get `LocallyCompactSpace` via `I.locallyCompactSpace` +
  `ChartedSpace.locallyCompactSpace`, cf. MetricPreconv.lean:126). Diagonalized
  property `P j φ` (net-time global tendsto + K_j net-conv order j) via
  `exists_diag_subseq` (MetricPreconvDiag.lean:50), with `hstep := netFullDiag`,
  `hsub`/`hextend` mirroring `netFullDiag`'s own stability blocks. Per-j net
  limits collapsed to ONE global `gNet` via `metric_ext_inner` +
  `tendsto_nhds_unique` (`hgNetUniq`).

## STATUS UPDATE — construction COMPLETE (no sorry)
`windowGInfAll` is fully proved with NO `sorry`/`admit`. The window-family
construction below was implemented in full. Focused read-only check
(`lake env lean`) is GREEN and warning-free. Authoritative `build +Module` +
`#print axioms` pending the global Lake lock (held by a concurrent agent's build
at handoff) — see Verification status.

Extra lemmas landed in the file (all sorry-free):
- `metricInnerApply_diff_le`: `|A.inner x v w - B.inner x v w| ≤ n · metricDerivNorm 0 A B gRef x
  · (gRef(v+w,v+w)+gRef(v,v)+gRef(w,w))` — polarization + `metricQuadFormDiff_le_metricDerivNorm`
  (AllTimesBoundsFlow, now imported) + `metric_add_self`.
- `metricInner_cauchy`: order-0 seminorm Cauchy ⇒ each scalar component `k ↦ (gk k).inner x v w`
  is a real CauchySeq (via `metricInnerApply_diff_le` + `Metric.cauchySeq_iff`).
- `metricLimit_uniq`: two metrics that are subsequential CLM-inner limits of a componentwise-Cauchy
  metric sequence are EQUAL (evaluate at v,w → scalar; `tendsto_nhds_of_cauchySeq_of_subseq`
  + `tendsto_nhds_unique`; `metric_ext_inner` + `ContinuousLinearMap.ext`).
- `windowGInfPt`: `windowGInf` re-derived exposing pointwise window conv + per-time inner tendsto
  (kept as a reusable convenience; NOT on `windowGInfAll`'s path).

Gotchas fixed during elaboration: (1) `abs_add` → `abs_add_le` (Mathlib rename);
(2) `hdense` yields `|t - e n|` so NO `abs_sub_comm` needed in the ball-cover step;
(3) redundant `ring` after a closing `field_simp` = "no goals" error — drop it;
(4) `add_le_add_right` arg-order surprise → use `linarith`; (5) `AllTimesBoundsFlow`
must be explicitly imported (not in `MetricPreconvWindowGInf`'s closure);
(6) the single global window family is `gAt0` (metricPreconvFull on `Kx 0`), and each
per-`j` `metricPreconvFull` limit is identified with it via `metricLimit_uniq` — this is
what dissolves the "limits don't glue" obstruction, using the GLOBAL net-time tendsto from
`netFullDiag` (uniqueness of `gNet`) + per-x Cauchy from `netCauchyAt (Kx m ∋ x)`.

## HISTORICAL: the frontier that WAS the `sorry` (now closed)
Build the single global window family `gInf t` from `gNet` and prove per-(K_j,j)
window convergence. Concretely:
1. `gInf t := metricPreconvFull (Kx 0) 0 (fun k => gSeq (φ k) t)` limit (global,
   all-x tendsto); off the window, `gRef`.
2. Per (K_j,j): `L_j` from `hgLip (Kx j) _ j`; `netCauchyAt (Kx j) ... j` (order-j
   metricDerivNorm Cauchy on Kx j at each window time); `metricPreconvFull (Kx j) j`
   → subseq ψ_j, limit gT_j t; `fullOfSubseq (Kx j) j` → full-φ order-j conv on
   Kx j to gT_j t.
3. UNIQUENESS `gT_j t = gInf t` GLOBALLY (all x, via `metric_ext_inner`):
   the full-φ inner sequence `fun k => (gSeq (φ k) t).inner x` is CauchySeq in the
   (complete, finite-dim) CLM space (from order-0 `netCauchyAt (Kx m)` at x ∈ Kx m,
   via `metricQuadFormDiff_le_metricDerivNorm` (AllTimesBoundsFlow.lean:111) on the
   diagonal + polarization for off-diagonal, cf. `metricDiff_comp_le`), so the two
   subsequence limits (gT_j, gInf) coincide by
   `tendsto_nhds_of_cauchySeq_of_subseq` (Mathlib Cauchy.lean:277) +
   `tendsto_nhds_unique`.
   Because gT_j t = gInf t GLOBALLY, jets agree ⇒ `metricDerivNorm a (...) (gInf t) x
   = metricDerivNorm a (...) (gT_j t) x`, transferring the fullOfSubseq conv.
4. Reduce arbitrary (K,p): pick j ≥ p with K ⊆ Kx j (`Kx.exists_superset_of_isCompact`
   + `Kx.subset` monotone to also swallow p ≤ j — take j := max of the two); apply
   the (Kx j, j) window conv at ε/2 pointwise, then `metricDerivNormSupOn_le_of_forall`
   (WindowPreconv.lean:187) gives sup ≤ ε/2 < ε. NO sSup monotonicity / BddAbove
   fight needed (this is why the per-j output must be POINTWISE, which windowGInfPt
   and the fullOfSubseq route both are).

The main labor is step 3's CLM-CauchySeq-from-bilinear-form-Cauchy (polarization)
and the metricPreconvFull/fullOfSubseq plumbing per j. Estimated a full focused
session. NOT a hidden mathematical wall — the route is fully identified and every
cited lemma exists; it is volume + careful CLM completeness bookkeeping.

## Verification status — DONE, axiom-clean
- Authoritative targeted build GREEN:
  `build +DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll`
  → "Build completed successfully (3885 jobs)"; this module built with no warnings (the only
  build warnings are pre-existing `show`-linter notes in other HCGCompactness files).
- `#print axioms windowGInfAll` = `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).
- No `sorry`/`admit` in the file.
- The file adds one instance hypothesis `[WeaklyLocallyCompactSpace M]` to `windowGInfAll`
  (needed by `CompactExhaustion.choice`); for a manifold over a finite-dim model this is
  discharged downstream via `I.locallyCompactSpace` + `ChartedSpace.locallyCompactSpace`.

## 2026-07-09: compact-open limit uniqueness API

Added `metricCInf_inner`, which turns `MetricCInfConvOnCompacts` into pointwise convergence of
every scalar metric-inner component, and `metricCInf_unique`, which proves uniqueness even when
the two convergence statements use different fixed reference metrics. Focused verification
passed without warnings or new `sorry`.
