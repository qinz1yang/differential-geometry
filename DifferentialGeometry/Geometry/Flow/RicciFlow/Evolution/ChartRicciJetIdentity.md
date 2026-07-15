# ChartRicciJetIdentity.lean — Lemma 3 + the chart-Gram glue chain (hglue / corollary (a))

Verified, sorry-free, banked (`lake build`, 3721 jobs). This file is the geometry-layer half of the
`hglue` junction-smoothness route (the C∞ glue across the singular time ω in `extends_of_rmBounded`).
See the memory note `hglue-splice-and-gates.md` for the full project context and the analysis-layer
halves (`Analysis/Calculus/TimeJet*`, `.../SmoothExtension/{MatrixInverseSmooth,ChartRicciJet,
JetPartialDeriv,JetGlueParam}`).

## What this file proves (bottom-up)

The abstract Ricci-flow operator `Φ = jetRicciFlow` (a function of the chart-Gram 2-jet, defined in
`ChartRicciJet.lean`) is connected to the geometric chart Ricci tensor, and the whole jet-match glue is
assembled:

- `chartGramPi g α` — the chart-Gram as a `Pi`-valued field `E → (Fin n → Fin n → ℝ)` (the value space
  of `jet2`; avoids putting a norm on `Matrix`).
- `jet2_chartGram_d1`/`_d2`/`_invGram` — the `jet2` slots of `chartGramPi` read off as
  `partialDeriv`/`chartInvGramOnE` (via the `JetPartialDeriv` bridges `fderiv_matEntry`/`fderiv2_matEntry`).
- `chartChristoffel_eq_jet`, `chartChristoffelDeriv_eq_jet` — the chart Christoffel / its `partialDeriv`
  equal the abstract `jetChristoffel`/`jetChristoffelDeriv` (via `partialDeriv_chartChristoffel_eq` +
  `partialDeriv_chartInvGramOnE_eq` + `gramBracket`/`gramBracketDeriv`, conversions as simp rules).
- `chartRiemann_eq_jet` → **`chartRicci_eq_jet`** (Lemma 3: `chartRicci = jetRicci(jet2 chartGram)`) →
  **`jetRicciFlow_chartGram`** (`Φ(jet) = −2·chartRicci`).
- `ricciFlowChartGram_jetMatch` — corollary (a) applied: two metric families, chart-Gram jointly C∞ on
  the half-slabs + chart-Gram Φ-evolution + seam boundary ⇒ equal one-sided time-jets (the splice `hjet`).
- `chartGramEvolution_of_pde` — chart-Gram entry PDE `∂ₜ(chartGram_{ik}) = −2·chartRicci_{ik}` ⇒ the
  Φ-form `∂ₜ(chartGram) = Φ(jet2 chartGram)`.
- `chartGramEntryPDE_of_metricPDE` — metric PDE `∂ₜ((g·).inner v_i v_k) = −2·ricciTensor` ⇒ the chart-Gram
  entry PDE, via `ricciTensor_chartBasisVec_alpha_eq` (off-centre α-chart Ricci bridge) +
  `chartGramMatrix = g.inner(chartBasisVecFiber)`.
- **`chartGramGlue_contDiffOn`** — THE `gram_smooth` CONTENT: `if t≤0 then chartGram(g₁) else
  chartGram(g₂)` is `C∞` on `univ ×ˢ V` (the frozen splice `contDiffOn_glue_of_jet_param` fed by the
  jet-match). Hypotheses `hL`/`hR`/`hcurve` are the BBS/DeTurck joint-smoothness gates.

## Gotchas (what tripped me up)

- Namespaces to `open`: `chartModelBasis` ∈ `…Integral.Measure`;
  `partialDeriv_chartChristoffel_eq`/`gramBracket`/`gramBracketDeriv` ∈
  `…PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients`; `ricciTensor_chartBasisVec_alpha_eq` ∈
  `…Integral.Connection`; `partialDeriv_chartInvGramOnE_eq` ∈ the file's own `…Integral.DivergenceTheorem`.
- `chartGramEntryPDE_of_metricPDE` needs `[I.Boundaryless] [SigmaCompactSpace M] [T2Space M]` (the
  closed-manifold Ricci symmetry behind the off-centre bridge).
- `omit` of `InnerProductSpace`/`Module.Finite`/`NeZero` FAILS on the leaf bridge lemmas (instance-synth
  references); the resulting unused-section-var warnings are benign and left in place.
- `smoothRiemannianMetricToInfty g = g` (DeTurckRHS.lean:36) — IDENTITY coercion between the two
  `SmoothRiemannianMetric` types; my lemmas use the `Integral.Measure` type, the construction's
  `g_fam`/`r` use the RicciFlow type — coerce through this `:=g` map.

## Handoff — what the collaborator's CinftyLimitGlue/MaximalTime needs to do

`CinftyGlueData.gram_smooth` is exactly `chartGramGlue_contDiffOn` applied to `g₁ = g_fam` (BBS limit)
and `g₂ = s ↦ r (s−ω)` (DeTurck restart), after the seam-shift ω→0. To call it, supply:
- `hL`/`hR` (joint C∞ of the two chart-Grams on `Iic 0 ×ˢ V` / `Ici 0 ×ˢ V`) = **Gate-L (BBS) / Gate-R
  (DeTurck)** — the cross-lane black boxes;
- `hcurveL`/`hcurveR` (the `jet2`-curves C∞) — follow from `hL`/`hR`;
- `hdet` (positive-definite Gram at the seam) — from the metric being Riemannian;
- `hevolL`/`hevolR` — via `chartGramEvolution_of_pde ∘ chartGramEntryPDE_of_metricPDE` from the
  construction's metric PDE (the BBS/DeTurck Ricci-flow equation), with `goodSet` membership and the
  `extChartAt` inverse;
- `hbdry` (seam metric match) — from `metric_match`/`tendsto_left`.
`gram_cont` (C⁰ up to the left endpoint) and `metric_match` are separate `CinftyGlueData` fields built
in CinftyLimitGlue.
