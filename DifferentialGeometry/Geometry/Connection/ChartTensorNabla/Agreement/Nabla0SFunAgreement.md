# Nabla0SFunAgreement — `nabla0SFun ↔ tensor0SCovariantDerivative` for `(0,s)` tensors

Home of the missing chart↔abstract agreement that gates
`HCGCompactness/MetricCovDerivBridge.lean` `normBridge` (item-6 brick 2a, D2).

Target lemma (directional, `r = 0`, all `s`):

```
nabla0SFun_eq_tensor0SCovariantDerivative
  (g : SmoothRiemannianMetric I M) (s : ℕ)
  (X : ContMDiffSection I E ∞ (TangentSpace I))
  (α : Tensor0SField … s) (x : M) :
  nabla0SFun s (LeviCivita g) X α x
    = tensor0SCovariantDerivative I M s (LeviCivita g) (fun y => α y) x (X x)
```

## ROUTE VERDICT (session, 2026-07-24): **route (i)** — `nabla0SFun = chartTensor0S`, then chain the sibling.

Evidence gathered in recon (all confirmed present in tree):

1. **Both formalisms share the identical `∂ − Σ_slot Γ` shape.**
   - `nabla0SFun` unfolds (via `mcovariantDeriv_tensor0SFromConnection` →
     `mcovariantDeriv_tensor0SWithin` → `covariantDeriv_tensor0SModelWithin`) and evaluates by
     `covariantDeriv_tensor0SModelWithin_apply_slots`
     (`Model/Tensor0S.lean:88`):
     `dα_X slots − Σ_a α (update slots a (ΓX (slots a)))`,
     with `dα_X = fderivWithin (tensor0SModelInChart) …` and
     `ΓX = connectionEndomorphismInChart(L) (LeviCivita g)`.
   - `chartTensor0SCovariantDerivative` evaluates by
     `chartTensor0SCovariantDerivative_succ_apply`
     (`Tensor0S/ChartTensor0SCovariantDerivative.lean:205`):
     `tensor0SIntrinsicChartCLM … (X b) slots
        − Σ_k T b (update slots k (chartLeviCivitaParallelCLM g α b X (slots k)))`
     (the `slotCLM`/`Function.update` shapes coincide exactly:
     `fun i => slotCLM k Φ i (m i) = Function.update m k (Φ (m k))`).

2. **Chart center = eval point is legal.** `self_mem_chartLeviCivitaGoodSet`
   (`LeviCivita/…`) gives `x ∈ chartLeviCivitaGoodSet x` unconditionally, so we
   may take chart center `α := x`.

3. **The sibling closes chart↔abstract.**
   `chartTensor0SCovariantDerivative_eq_abstract_zero` (base) /
   `…_succ` (`Agreement/ChartTensor0SCovariantDerivativeAgreementSucc.lean`) give
   `chartTensor0S s g α T X b = tensor0SCovariantDerivative I M s (LeviCivita g) T b (X b)`
   for `b ∈ chartLeviCivitaGoodSet α`.  So the ONLY new content is the crux
   `nabla0SFun = chartTensor0S` at matching chart center.

The crux splits into two ingredient bridges, both with existing infrastructure:

- **(A1) intrinsic pieces.**  `fderivWithin (tensor0SModelInChart s x …)` (nabla side)
  vs `tensor0SIntrinsicChartCLM`/`fderiv (tensor0SChartE_section_repr ∘ symm)` (chart
  side).  Both are the Fréchet derivative of "trivialize the section then pull back
  through the chart inverse" in the SAME tensor-bundle trivialization at the center
  (`Tensor0SSpace s I x := Bundle.continuousMultilinearMap ℝ s E (TangentSpace I) x`;
  `tensor0SModelAt_apply` (`FixedChart/Models.lean:41`) unfolds `tensor0SModelAt` to
  `A (fun a => (trivAt E (TangentSpace I) x₀).symmL x (slots a))`; the chart repr uses
  `.continuousLinearMapAt` of the same trivialization).  Bridge = trivialization
  identity + `Trivialization.continuousLinearMapAt_apply`.  NEW but mechanical.

- **(A2) Christoffel endomorphisms.**  For a chart-CONSTANT section the `fderiv`
  vanishes, so `LeviCivita_chart_apply` + `chartLeviCivita_apply` give the linchpin
  `LeviCivita g (tangentConstInChart w) x v = trivFromE(christoffelCorrection g x x w v)`.
  Hence `connectionEndomorphismInChart (LeviCivita g) X x (center)` reduces (through
  `connectionEndomorphismInChartL_apply_center` and the `trivToE/trivFromE` inverse) to
  `christoffelCorrection g x x`.  Matching to `chartLeviCivitaParallelCLM` needs the
  lower-index Christoffel symmetry `chartChristoffel_symm` (torsion-free), which EXISTS
  (`…GreenDivergenceIdentity.lean:272`).  NEW but each step is a cited one-liner.

Route (ii) (mirror the succ induction directly for `nabla0SFun`) was REJECTED:
`nabla0SFun` is defined non-recursively in `s` (single model formula), so it carries no
`nabla0SFun (s+1) = f(nabla0SFun s)` recursion to feed an IH — route (ii) would first
have to BUILD that recursion (a partial-eval decomposition of `covariantDeriv_tensor0SModelAt`),
strictly more work than reusing the sibling.

Component cross-check available: `nabla0SFun_eval_coordFrame`
(`Coordinates/NablaComponents/CoordFrameStep.lean:51`) already gives the `∂ − Σ Γ`
coordinate-component form of `nabla0SFun`, confirming the shape.

## Honest effort assessment
Sibling-sized (~300–500 line) assembly.  Math route fully confirmed; principal risk is
trivialization/`continuousLinearMapAt`-vs-`.2` bookkeeping in (A1) and the `trivToE∘trivFromE`
cancellation in (A2), plus slow heavy-import checks.  No convention/slot-order/sign mismatch
remains (all resolved).  If the assembly does not close within budget, the honest fallback is
to leave `normBridge`'s existing documented sorry untouched (do NOT create a fake-progress
wrapper that merely relocates the sorry) and report confirmed feasibility + this recipe.

## OUTCOME (2026-07-24): agreement PROVED, axiom-clean — via a cleaner route than (i)

`nabla0SFun_eq_tensor0SCovariantDerivative` is proved sorry-free.  `lake build`:
"Build completed successfully (3680 jobs)".  Axiom audit (both the endpoint and its
engine lemma): `[propext, Classical.choice, Quot.sound]` — NO `sorryAx`.

**The actual route was better than route (i): it bypasses `chartTensor0S` and the sibling
entirely.**  Both formalisms already have a *closed intrinsic* evaluation on smooth slots:

- `nabla0SFun_eval_smooth_slots` (`NablaOnTensors/Regularity/Tensor0S.lean:651`):
  `(∇α)(V·) = ∂_X(α(V·)) − Σ_a α(…, ∇_X V_a, …)`.
- The abstract side is shown to satisfy the SAME closed form by a new engine lemma
  `abstractDerivEval_aux` (this file): the tensor-derivation / Leibniz rule for
  `tensor0SCovariantDerivative`, proved by induction on `s` from the Hom-bundle product
  rule `homBundleCovariantDerivativeFun_apply_eq` (`Realization/HomNabla.lean:264`) +
  `tensor0SCovariantDerivative_succ_apply` + curry/`Fin.cons`/`Fin.sum_univ_succ`
  bookkeeping.  The two closed forms match verbatim; realising an arbitrary slot tuple
  by smooth sections (`ContMDiffSection.exists_eq_at`, at level `(⊤ : ℕ∞) = C^∞`) and
  `ContinuousMultilinearMap.ext` closes the agreement.

So the plan's (A1) intrinsic-chart bridge and (A2) chart-Christoffel bridge were **not
needed** — the intrinsic `nabla0SFun_eval_smooth_slots` form + the abstract Leibniz rule
sidestep all chart/trivialisation/Christoffel bookkeeping.  Route (i) would also have
worked but is strictly more machinery.

### Main declarations (this file)
- `abstractDerivEval_aux (cov) [ContMDiffCovariantDerivative cov ∞] : ∀ s T V X …, ` the
  abstract `(0,s)` covariant derivative on smooth slots equals
  `extDerivFun(T(V·)) x (X x) − Σ_a T x (update (V·x) a (cov (V a) x (X x)))`.  Reusable
  intrinsic Leibniz rule (previously missing).
- `nabla0SFun_eq_tensor0SCovariantDerivative (g s X α x) :
  nabla0SFun s (LeviCivita g) X α x = tensor0SCovariantDerivative I M s (LeviCivita g) (fun y => α y) x (X x)`.

### KEY LESSONS
- **`set_option backward.isDefEq.respectTransparency false` is REQUIRED** to synthesize
  `NormedSpace ℝ (Tensor0SModel s ℝ E)` when writing `𝓘(ℝ, Tensor0SModel s ℝ E)` (needed
  for any `ContMDiff`/`MDifferentiableAt` on the `(0,s)`-bundle in a fresh file).  Without
  it, even an explicit `letI` of the exact instance is ignored (`Tensor0SModel` is a
  reducible def; synth won't unfold it without permissive transparency).  Every existing
  file that touches these models sets this option.  Cost me the longest detour — the
  error looks like a missing instance / import poison but is a transparency setting.
- `ContMDiffCovariantDerivative` lives in the `CovariantDerivative` namespace — qualify it
  (`CovariantDerivative.ContMDiffCovariantDerivative`) or `open CovariantDerivative`.
- `ContMDiffSection.exists_eq_at` takes `n : ℕ∞`; pass `(n := (⊤ : ℕ∞))` to obtain a
  `C^∞` section (`(∞ : WithTop ℕ∞) = ↑(⊤ : ℕ∞)` in this codebase, NOT `⊤ : WithTop ℕ∞`).
- `lake env lean` false-FAILED the whole file while dependency oleans were stale; the
  authoritative `lake build` (which replays/refreshes them) was the reliable signal.

## Status
- 2026-07-24: **DONE.**  `nabla0SFun_eq_tensor0SCovariantDerivative` proved & axiom-clean.
  Downstream: use it to discharge `HCGCompactness/MetricCovDerivBridge.lean` `normBridge`
  (see that file's `.md`).
