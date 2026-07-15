# LimitSolutionEquation.lean — P4 Brick 6 `equation` bridge (2026-07-02)

MSM135 chapter3.tex:853–856 ("all derivatives of the metric converge ⟹ Ricci of
`g_k(t)` converges to Ricci of `g_∞(t)` ⟹ the limit is a solution"), as a generic
fixed-manifold theorem.  **Verified: targeted build green (3888 jobs), all four
endpoints axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).**
No `sorry` anywhere in the file.

## What is PROVED vs what is HYPOTHESIZED

Step 1 (derivative passage) is **fully proved**; step 2 (uniform Ricci
convergence from C²-metric convergence) is a **precisely-stated explicit input**
`hRicConv`, per the plan's fail-loud fallback — NOT a `sorry`, not a wrapper
that re-names the goal.  See "The missing conversion lemma" below for the exact
diagnosis of why step 2 could not be discharged from existing API.

## Declarations

1. `hasDerivWithinAt_lim` — **generic 1-D uniform-limit derivative passage on a
   convex set** (pure real analysis, no manifold).  If `f k` has derivative
   `f' k u` within convex `s` at every `u ∈ s`, `f' → h` uniformly on `s`
   (ε–k0 form), `f → g` pointwise on `s`, then `HasDerivWithinAt g (h t) s t`
   for every `t ∈ s` — closed-interval ENDPOINTS INCLUDED.  Mathlib's
   `hasDerivAt_of_tendstoUniformlyOn` requires an OPEN set (checked:
   `UniformLimitsDeriv.lean` has only `IsOpen`/`𝓝 x` versions), so this is
   proved by hand: `hasDerivWithinAt_iff_isLittleO` + `isLittleO_iff`, mean
   value inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on the
   Cauchy pair `f k0 − f m`, limit `m → ∞` via `le_of_tendsto`, then the
   3-term triangle split with constants `2ε + ε + ε` at `ε = c/4`.  No
   continuity of the derivatives needed, no FTC, no measurability side goals.
2. `metricInner_tendsto` — pointwise coefficient convergence
   `(gk k).inner x v w → gLim.inner x v w` from order-0 seminorm smallness
   `metricDerivNorm 0 (gk k) gLim gRef x → 0`, via the polarization bound
   `metricInnerApply_diff_le` (MetricPreconvWindowAll.lean) + `squeeze_zero`.
3. `metricLimit_pde` — **the core bridge.**  Inputs: `S : (k) → SolutionOn (D k)`,
   `hS k : IsSolutionOn (S k)`, `hreg : Icc β ψ ⊆ (D k).regular`, a limit family
   `gInf : ℝ → SmoothRiemannianMetric I M`, fixed `x v w`, `hinner` (pointwise
   inner convergence on the window), `hRicConv` (uniform-in-t Ricci coefficient
   convergence on the window — THE step-2 input).  Conclusion at every
   `t ∈ Icc β ψ`:
   `HasDerivWithinAt (fun s => (gInf s).inner x v w)
      (-2 * ricciTensor (gInf t) x v w) (Set.Icc β ψ) t`.
   Needs `[NeZero (Module.finrank ℝ E)]` (from the two-worlds Ricci bridge).
4. `metricLimit_pdeOn` — endpoint in the `windowGInfAll` consumption shape:
   replaces `hinner` by the POINTWISE form of the window seminorm convergence on
   a compact `K ∋ x` (`∀ p, ∀ ε > 0, ∃ k0, ∀ k ≥ k0, ∀ t ∈ Icc, ∀ a ≤ p,
   ∀ z ∈ K, metricDerivNorm a (gk t) (gInf t) gRef z < ε`); consumes only the
   `(p, a, z) = (0, 0, x)` instance.  `hRicConv` unchanged.

## Per-k equation extraction (step 1 plumbing)

`IsSolutionOn.equation → metric_derivWithin_eq_neg_two_ricci` (Basic/Core.lean:909)
gives `HasDerivWithinAt (fun s => (S.family.metric s).inner x v w)
(−2 · S.ricciAt t x (vec2 v w)) D.carrier t` at regular `t`.  Then:
- data-field Ricci → canonical: `S.ricciAt t x (vec2 v w) = ricciTensor
  (S.family.metric t) x v w` is EXACTLY `metricRicciAt_apply_eq_ricciTensor`
  (`Geometry/Curvature/MetricLeviCivitaReconcile.lean:163`, hypothesis-free) —
  `SolutionOn.ricciAt` is definitionally `metricRicciAt ∘ base.metric`, and
  `family_metric` is `rfl`; a `have h0' : … := h0` defeq re-typing makes the
  rewrite syntactic.  (`solnRicField_eq_ricciAt` / `solnMetricDeriv` were NOT
  needed — they bridge to the bundled section, one layer above what we need.)
- window restriction: `HasDerivWithinAt.mono` along
  `Icc β ψ ⊆ regular ⊆ carrier` (`RealTimeInterval.regular_subset` is a
  structure field).

## Interface choice: pointwise seminorm form, not `metricDerivNormSupOn`

`windowGInfAll`'s conclusion is `metricDerivNormSupOn K p … < ε` (an ℝ-`sSup`).
Extracting per-point smallness from it needs `BddAbove` of the defining set
(`le_csSup`), and NO BddAbove/continuity API for `metricDerivNorm` exists in the
tree (checked: the only pointwise-≤-sup lemma, `AllTimesBoundsFlow.lean:374`, is
`[CompactSpace M]`/`Set.univ`/`gRef = gInf`-specific, proved from equivalence
bounds, not continuity).  So `metricLimit_pdeOn` takes the POINTWISE form —
which is what `windowGInfAll`'s internal diagonal actually proves before it
csSup-packages (its per-`j` `P` predicate is pointwise).  Consumer note for
Brick 5: either add a pointwise-conclusion variant `windowGInfAllPt` (its proof
already holds the facts), or discharge `BddAbove` from the Brick-4 equivalence
bounds.  Do NOT try `le_csSup` without boundedness: `Real.sSup` of an unbounded
set is junk `0` and the sup-form hypothesis is then vacuously small.

## ★ The missing conversion lemma (step 2 diagnosis — for the future producer)

**DISCHARGED (2026-07-02): the producer now exists — `RicciFromJets.lean`
(`ricciConv_of_dnConv` matches `hRicConv` verbatim; per-pair core
`ricciSub_le_dNorm`; the conversion lemma below is `jet2Diff_le_dNorm`, proved
via the P3 tower identity `fderiv_chartRep_eq_towerStep`, NOT new chart-jet
calculus).  Correction to diagnosis (a).2 below: a PUBLIC quantitative twin of
the private chartRicci chain exists in
`Analysis/Spectral/Intrinsic/DeTurckCoefficients/` (`ChristoffelPerturbation`,
`RicciDiffAffine`, `InverseGramPerturbation`) — only its `exists_*_on_compact`
wrappers are per-pair; the pointwise lemmas re-assemble pair-uniformly.  See
`RicciFromJets.md`.  The diagnosis below is kept for the record.**

`hRicConv` (uniform-in-t `ricciTensor (gk t) x v w → ricciTensor (gInf t) x v w`
from `metricDerivNorm a ≤ 2` smallness on a neighborhood + equivalence) could
NOT be produced from existing API.  Both plan routes were investigated to the
exact blocking declarations:

- **(a) Chart route.**  The manifold→chart reduction IS available and public:
  `ricciTensor_eq_chartRicciSwap_of_basis_identity`
  (`Geometry/Connection/ChartBridge/Ricci.lean:301`) +
  `chartRiemannBasisIdentity_holds` (unconditional), which writes
  `ricciTensor g x v w = Σᵢₖ repr·repr·chartRicciTensor g x i k (extChartAt I x x)`
  with k-independent coefficients.  TWO gaps block the rest:
  1. **covariant→chart-jet conversion (the genuine missing lemma):** nothing
     converts `metricDerivNorm a (g, h, gRef)`-smallness near `x` into
     closeness of `iteratedFDeriv ℝ a (chartGramOnE … ) (extChartAt I x x)`
     for `a ≤ 2`.  The AA machinery's only covariant↔coordinate bridge is
     `metricDerivNorm_le_compSq_uniform` (`MetricPreconvBridge.lean:76`), which
     goes the OTHER direction (covariant ≤ frame-component ℓ², for the AA
     output leg) and through `component0S` frame components, NOT chart-Gram
     `iteratedFDeriv`.  `chartGramOnE` also has no linearity/`_sub` API (it is
     metric-nonlinear only through the chart pullback; a difference lemma
     would be provable but does not exist).
  2. **private, continuity-only chart-Ricci internals:** the entire chain
     `partialDeriv_chartGramOnE/chartInvGramOnE/chartChristoffel_continuous_of_hC2
     → chartRiemannTensor_continuous_of_hC2 → chartRicciTensor_continuous_of_hC2`
     (`ShortTimeAssembly/RicciContinuityInMetricTime.lean:220–371`) is
     `private` in `RicciContInMetricAux` and stated as `ContinuousOn` in the
     TIME parameter of one family — there is no sequence/uniform/quantitative
     version, and reusing it would mean publicizing + rebuilding ~4 lemmas in
     modulus form (inverse-Gram product rule included).
- **(b) Covariant difference estimate** `‖Ric(g)−Ric(h)‖ ≤ C(equiv)·Σ_{a≤2}
  metricDerivNorm a g h gRef`: no difference-of-connections tensor calculus
  exists anywhere in the tree (this is the classical `∇ᵍ−∇ʰ` tensor route); it
  would be a new multi-session layer.

**Smallest unblocking lemma** (recommendation, route (a)): for a FIXED chart
`α := x` and `a ≤ 2`, a quantitative
`‖iteratedFDeriv ℝ a (chartGramOnE g α i j − chartGramOnE h α i j) y‖ ≤
C(α, cpt) · sup_{z ∈ nbhd} Σ_{b ≤ a} metricDerivNorm b g h gRef z`
(constant independent of `g, h`) — the "chart jets of a (0,2)-difference are
controlled by covariant jets" estimate.  With it, sequence-uniform chart-Ricci
convergence follows by re-running the (then to-be-publicized) chartRicci
algebra with uniform bounds from `MetricUniformEquivalentOnWindow`
(`AllTimesBounds.lean:612`) for the inverse-Gram leg.

## Lean gotchas (this pass)

- Mathlib rename: `abs_add` is gone; the triangle inequality is `abs_add_le`
  (generated by `to_additive`, so `grep "theorem abs_add"` finds nothing —
  check use sites, e.g. `AbsoluteValue/Basic.lean:274`).  `abs_sub_le` is fine.
- `metricDerivNorm` nonnegativity: `Real.sqrt_nonneg _` works by DEFEQ in
  term position (`have hnn : 0 ≤ metricDerivNorm … := Real.sqrt_nonneg _`) but
  NOT as a `rw`/`abs_of_nonneg (Real.sqrt_nonneg _)` pattern (syntactic
  mismatch `|√?|` vs `|metricDerivNorm …|`).  Name the `have`, then rewrite.
- `squeeze_zero` with a metavariable middle function (`refine … (fun k => ?_) ?_`)
  can fail to unify; state the bound function explicitly in a `have` and apply
  `squeeze_zero` in term mode.
- The `RegularTime` subtype coercion `↑⟨u, h⟩` in the instantiated equation is
  handled by one defeq re-ascription `have h0' : HasDerivWithinAt … u := h0`,
  after which the value rewrite is syntactic.
- `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` argument order: receiver
  is the convexity (`hs.…`), then `hf bound xs ys` with `xs` the SUBTRACTED
  point (`‖f y − f x‖`).

## Verification

Focused check green; targeted build
`+DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.LimitSolutionEquation`
green (3888 jobs, module freshly compiled); `#print axioms` on all four
endpoints = `[propext, Classical.choice, Quot.sound]` (temporary prints,
output read from the build log, removed, clean rebuild green).
