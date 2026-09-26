# B6g1 — DESIGN_B6D_GLUE bricks B1, B2, B3, B12 (2026-09-26)

- Start. Read DESIGN_B6D_GLUE.md (whole), OPUS_FILL_LOG_B6D.md, OPUS_FILL_LOG_B6B3.md,
  `Surgery/Topology/TracedRegionAncientLimitWitnesses.lean` (lemmas 3/4), AGENTS.md (pc3: no
  header, no module docstring, no comments).
- Method per brick: statement + proof in a scratch probe under `%TEMP%/claude/b6g1`,
  `LEAN_NUM_THREADS=2 lake env lean`, then the real file; `#print axioms` and `#lint` only in scratch
  copies. Nothing registered in the root aggregate; nothing staged.

## B1 — DONE
- File `Topology/Sequences/ExceptionalSetApproximation.lean` (24 lines), root namespace.
- `exists_tendsto_forall_notMem_of_finite_diff_Icc` — exactly the §2 statement
  (`σ n ≤ s ∧ σ n ∉ E n` for EVERY `n`, `σ → s`). Proof: `σ n` picked in
  `Ioo (min s (-ζ n) - 1/(n+1)) (min s (-ζ n))` off the finite set, squeeze.
- Deviation: name `not_mem` → `notMem` (current Mathlib spelling; `not_mem` names are deprecated).
- Mathlib search: no such lemma (grep `exists_tendsto_forall_not*`, `Ioo_infinite … sdiff`).
- In-repo compile: rc 0, no output. Axioms `[propext, Classical.choice, Quot.sound]`. `#lint` 0/1.

## B2 — DONE
- File `Estimates/RicciLowerMetricComparison.lean` (81 lines), namespace
  `DifferentialGeometry.PDE.RicciFlow`; imports `Solution.Basic` only.
- `metric_inner_le_exp_mul_of_ricci_lower_bound` — exactly the §2 statement. Mirror of
  `Perelman.KappaSolutions.metric_inner_lower_bound_of_ricci_upper_interior`
  (`KappaSolutions/TerminalMetricLowerBound.lean`, the other one-sided bound):
  `e^{-2δ(s-a)} g_s(u,u)` antitone via `metricDerivAt`.
- Search: `metric_inner_exp_bounds_of_curvature_bound` (two-sided, `|Rm|`), `KLim…`,
  `inner_le_exp_mul_inner_of_abs_deriv_le` (two-sided); no one-sided Ricci-lower version existed.
- In-repo compile: rc 0, no output. Axioms `[propext, Classical.choice, Quot.sound]`. `#lint` 0/2.

## B3 — DONE
- File `Geometry/Curvature/CurvatureOperator/RicciLowerBound.lean` (44 lines), namespace
  `DifferentialGeometry.Geometry.Curvature`, any dimension:
  - `sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt`:
    `curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ →
     SectionalBoundedBelowAt g x (-δ)`.
  - `neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt`:
    `-((finrank E - 1) * δ) * g u u ≤ metricRicciAt g x (vec2 u u)` (reuses
    `Riemannian.ricci_lower_of_sectionalBoundedBelowAt` + `metricRicciAt_apply_eq_ricciTensor`).
- File `Perelman/CanonicalNeighborhood/PinchingRicciLowerBound.lean` (48 lines):
  - `FiniteHorn.neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt` — exactly
    the §2 statement (3-D corollary of the general one).
  - `Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto` — exactly the §2 statement;
    deviation: namespace `…RicciFlow.Perelman` (home of `AdmissiblePinchingFunction`) instead of
    `FiniteHorn`; it resolves unqualified from inside `FiniteHorn`.
- Deviation (placement only): §2 routed the first theorem through
  `curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le`; the sectional route is shorter and gives
  the general-dimension theorem, the 3-D statement is its corollary.
- Compile: `RicciLowerBound.lean` in-repo rc 0, no output. `PinchingRicciLowerBound.lean` imports it
  (no olean) → scratch concatenation of both: no output. Axioms of all 4: `[propext,
  Classical.choice, Quot.sound]`. `#lint` 0/4.

## B12 — DONE (new theorems, old ones untouched)
- File `Surgery/Topology/TracedRegionAncientLimitDerivativeCutoff.lean` (136 lines), imports
  `TracedRegionAncientLimitWitnesses` (uncommitted, no olean).
  - `ObservedHistory.abs_derivWithin_scalar_le_of_survivor_maps_of_lt` (lemma 3 with cutoff):
    `hstage` over `v < t₀`; new hypothesis `hst₀ : t + s/R < t₀`; `hs : s ∈ Ioc (-θ) 0` (was
    `Ioo`; `s = 0` is now allowed, `t < t₀` is then forced by `hst₀`). Rest verbatim.
  - `RetainedCoreHistory.abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt`
    (lemma 4 with cutoff): `hcurrent`/`hfinal : DerivativeBoundBefore Ctime qcan t₀`, conclusion for
    `v < t₀`; added `ht₀ : t₀ ≤ t` (needed for `activeStage v ≤ activeStage t`; B13 has
    `ht₀ : t₀ n ≤ t n`). Its conclusion is literally lemma 3′'s `hstage` (with `C = Ctime`).
  - The private window lemma is inlined (no `open private`).
- Compile: scratch concatenation Witnesses + this file: no output. Axioms of both
  `[propext, Classical.choice, Quot.sound]`. `#lint`: only docBlame on the Witnesses def (excluded).

## Summary
- 5 new files, 333 lines; 9 public theorems; no sorry/axiom/nolint/heartbeat options; names unique;
  no lines > 100 except imports. Not registered in `DifferentialGeometry.lean` (lane rule).
