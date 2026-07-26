# VOLUME COMPARISON V0 — Integration-layer API brick (executor kickoff prompt)

**Paste everything below the line into the new session (Opus).  Self-contained.
Written 2026-07-07 by the planning lane, after verifying the V1a gap reported
in `Geometry/Comparison/Volume/NormalChartMeasure.md`.**

---

You are implementing **brick V0 of
`DifferentialGeometry/Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`** in the
Lean 4 project at `E:\testdifferential-geometry`: the missing Integration-layer
theorem that evaluates `riemannianVolumeMeasure` through an arbitrary `C¹`
coordinate parametrization.  Read first, in order: `CLAUDE.md` (binding
workflow rules), `important_lesson.md`, `VOLUME_COMPARISON_PLAN.md` (§0 +
§Stage V0), `Geometry/Comparison/Volume/NormalChartMeasure.md` (the gap audit
and the planner ruling — the gap is verified; do NOT re-audit it).  Use
`./scripts/lake-locked.ps1` for all Lake operations (claim files, focused
checks, targeted `build +Module` verification; never raw `lake`).  Other
agents are active under `Geometry/Flow/**` — do not touch anything there.

## Target

ONE new file `DifferentialGeometry/Analysis/Integration/Measure/ParamEvaluation.lean`
(you MAY edit other `Analysis/Integration/Measure/*` files only to generalize
a private helper; keep every existing public statement unchanged), delivering:

1. `paramGramMatrix (g) (Ψ) : E → Matrix (Fin n) (Fin n) ℝ` — the pulled-back
   Gram matrix of a parametrization `Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1`
   at `w ∈ Ψ.source`: entries `g_{Ψ w} (mfderiv 𝓘 I Ψ w (e i)) (mfderiv 𝓘 I Ψ w (e j))`
   against a fixed orthonormal basis `e` of `E` (mirror `chartGramMatrix`'s
   design in `Measure/ChartDensity.lean`, but defined directly from `mfderiv`
   of `Ψ`, NOT through `trivializationAt`).  Plus `paramDensity g Ψ w :=
   Real.sqrt (paramGramMatrix …).det`, positivity on the source, and
   continuity on the source (from `Ψ`'s `C¹` regularity + `g.contMDiff`).
2. The **evaluation theorem** (the deliverable):
   for measurable `B ⊆ Ψ.source`,
   `riemannianVolumeMeasure g ((Ψ : E → M) '' B)
      = ∫⁻ w in B, ENNReal.ofReal (paramDensity g Ψ w) ∂(modelHaar)`
   (match the layer's Haar-measure name/vocabulary — `modelHaar` appears in
   `Measure/Invariance.lean`).  Ambient hypotheses: exactly those of
   `riemannianVolumeMeasure` (`T2Space M`, `SigmaCompactSpace M`,
   finite-dimensional inner-product model) — weakest assumptions, `C¹` on `Ψ`,
   NOT smoothness.
3. A convenience corollary in set form:
   for measurable `A ⊆ Ψ.target`,
   `riemannianVolumeMeasure g A = ∫⁻ w in (Ψ.symm : M → E) '' A, …` —
   derive from 2 via the partial-equiv image/preimage algebra; do not prove it
   independently.

**Statement-audit rule (binding):** before proving, each public statement gets
a docstring: why true, under which regularity, who consumes it (V1a at
`Ψ := expMapDiffeo g x`; V2a polar; entropy integrals).

## Proof route (planner-fixed; deviations allowed only with a recorded reason)

Stage the proof as FOUR named lemmas — do not inline them into one monolith:

- **V0a Gram transformation law.**  For `w ∈ Ψ.source` with `Ψ w` in the
  `x₀`-canonical chart's base set, writing `T := (transition) = extChartAt/
  trivialization coordinates of Ψ` (the `E → E` composite the layer already
  uses — mimic how `Measure/Invariance.lean` forms canonical transitions):
  `paramGramMatrix g Ψ w = (D T w)ᵀ * chartGramMatrix g x₀ (Ψ w)-matrix * (D T w)`
  in matrix form, hence
  `paramDensity g Ψ w = |det (D T w)| * chartDensity g x₀ (Ψ w)`.
  This generalizes the existing canonical-pair transition-density identity
  (`Measure/Invariance.lean` :349–:548) — read its proof FIRST and reuse its
  linear-algebra lemmas (`Matrix.det_transpose`, congruence-determinant
  algebra) rather than re-deriving them.
- **V0b canonical-chart change of variables.**  For measurable
  `B' ⊆` (the overlap, inside `Ψ.source` with image in the `x₀` base set):
  `∫⁻ over chart-image of (Ψ '' B') of (pou_{x₀} · chartDensity) = ∫⁻ over B'
  of (pou_{x₀} ∘ Ψ) · |det D T| · chartDensity ∘ …` via Mathlib's Jacobian
  change of variables (`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
  `Mathlib/MeasureTheory/Function/Jacobian.lean`).  Inputs it needs: `T`
  injective on the overlap (both factors are partial homeo/diffeos) and
  `HasFDerivAt`/`HasFDerivWithinAt` of `T` there (from `Ψ`'s
  `contMDiffOn_toFun` at `C¹` + the chart's smoothness; the layer's existing
  `aemeasurable_extChartAt_symm_restrict_target`-style helpers handle the
  measurability side).
- **V0c single-chart evaluation through `Ψ`.**  Combine
  `chartLocalMeasure_lintegral_U_eq_setLIntegral_image`
  (`Measure/Invariance.lean:736`) with V0a+V0b: the `x₀`-chart-local piece of
  the measure of `Ψ '' B` equals `∫⁻ w in B, (pou_{x₀} (Ψ w)) ·
  ofReal (paramDensity g Ψ w)`.
- **V0d recombination.**  Sum V0c over the canonical POU
  (`riemannianVolumeMeasure_def`, the tsum/finset machinery at
  `Invariance.lean` :938–:1003 and `FamilyDecomposition.lean`
  `riemannianVolumeMeasure_eq_finset_sum`), using `Σ pou = 1` — target
  statement 2, then 3.

## Boundaries and gotchas

- Do NOT touch `Geometry/Flow/**`, `Geometry/Comparison/Volume/*` (that is the
  V1 lane, resumed after this brick), or public statements of existing
  Integration files.
- `ENNReal`/`lintegral` throughout (the layer's convention); convert to Bochner
  integrals only if an existing lemma forces it, and locally.
- `lake env lean` success is untrustworthy (cached false-green); verify with
  `./scripts/lake-locked.ps1 build +DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation`.
- Heavy-not-looping elaboration: per-declaration
  `set_option maxHeartbeats 800000 in` with a one-line comment is acceptable.
- `λ` is a Lean keyword — never in identifiers.
- Instance-synthesis timeouts on tensor goals → `important_lesson.md`
  ("Tensor model aliases and typeclass synthesis") before restructuring.
- If Mathlib's Jacobian change-of-variables genuinely cannot accept the `T`
  you can produce (e.g. an `ae`-differentiability mismatch), STOP and report
  the exact lemma + goal — do not build a private change-of-variables theory.

## Acceptance and handback

Sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`), green via
the targeted `lake-locked build`, same-name `ParamEvaluation.md` note (route,
failures, verification status — no logs).  Report: exact public statements
(names + hypotheses), which existing Invariance/ChartDensity lemmas were
reused vs. generalized, deviations from V0a–V0d and why, and the honest
distance to V1a (which should then be a one-line specialization).  If blocked,
classify the failure (math / route / missing API / typeclass / performance /
tooling) with the exact goal and error, and stop rather than hiding the
obligation behind a new hypothesis.  Do not stop on a green intermediate tree
with an obvious next lemma.  Progress framing: V0 is one brick under Stage V1
of the volume-comparison lane (P1a of `Geometry/Flow/RicciFlow/POINCARE_PLAN.md`);
a green V0 unblocks V1a but leaves Stage V1 (V1b–V1d) and Stages V2–V3 open —
report percentages accordingly.
