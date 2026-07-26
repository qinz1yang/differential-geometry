# MetricPreconv — MSM135 Corollary lbl351 (metrics with bounded derivatives preconverge)

**Status: Bricks A1 + A2 DONE + verified; Brick B PRODUCER + PER-CHART
CONVERGENCE DONE + verified; Brick C-I = C0 (`exists_diag_subseq`) DONE in
`MetricPreconvDiag.lean`, C1a/C1b STOPPED (planner decision) (2026-06-12).**

## Brick C-I status (2026-06-12) — see MetricPreconvDiag.md

- **C0 `exists_diag_subseq` DONE** (`MetricPreconvDiag.lean`, sorry-free,
  axiom-clean): the abstract countable common-subsequence diagonal, proved as the
  planner fixed it.  Usable with `hstep := exists_chart_cInfConv`,
  `hsub := MapCInfConvOnCompacts.comp_subseq`, `hextend` = the `∃k₀` shape.
- **C1a / C1b STOPPED — planner decision.**  The `gInf : SmoothRiemannianMetric`
  packaging needs the inverse of the `componentize` layer (build a smooth
  intrinsic `(0,2)` field / `ContMDiffRiemannianMetric` — intrinsic `inner` CLM +
  `contMDiff` bundle section — from a chart-compatible family of `ContDiff`
  component functions).  That bridge does NOT exist; the project documents the
  general gate as unavailable (`NonlinearitySpectral.lean:53`), and the only
  realization (`exists_smooth_metric_of_smooth_tensor_small`) is a
  compactly-supported, fibre-small perturbation consuming an intrinsic
  `SmoothCcTensor`, not chart components / a global limit.  Full analysis + the
  located building blocks (`compactCovering`, `exists_chart_cInfConv`,
  `exists_diag_subseq`) + planner options are in **MetricPreconvDiag.md**.

## Brick B PRODUCER + per-chart convergence DONE (MetricPreconv.lean)

Producer chain (all `#print axioms` clean = `[propext, Classical.choice,
Quot.sound]`, targeted build green 3845 jobs, 2026-06-11):

- `metricComp_iteratedFDeriv_le (gRef gSeq) (hbdd : ∀ q K, IsCompact K → ∃ C, ∀ k,
  ∀ z∈K, metricCovDerivNorm q (gSeq k) gRef z ≤ C) (x₀) {Kc} (hKc hKchart)
  (V : Fin 2 → section) (r) : ∃ Mr, 0 ≤ Mr ∧ ∀ k, ∀ y∈Kc, ‖∇ʳ (chartRep of the
  covariant component of gSeq k) (extChartAt y)‖ ≤ Mr` — the **k-uniform** chart
  bound.  Proof: A2 gives `CV`; `hbdd` gives `C q`; `b q := max (C q) 0`,
  `Mr := CV·∑_{q≤p+r} b q`; the A2 hypothesis `√normSq ≤ b q` follows by
  `simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]`.  Note
  `covDerivOfField gRef A0 0 = A0` so p=0 IS the metric component.
- `exists_chart_engineInput (… V {K₀} hK₀ hK₀chart) : ∃ (Φ : ℕ→E→ℝ) (χ : E→ℝ),
  (∀k, ContDiff ⊤ (Φ k)) ∧ (∀r, ∃M, ∀k x, ‖∇ʳ(Φ k) x‖ ≤ M) ∧ (∀y∈K₀, χ(extChartAt
  y)=1) ∧ (∀k, Φ k = fun x => χ x · chartRep(gSeq k) x)` — the literal
  `exists_cInf_subseq` input: globally smooth maps with `r`-by-`r` K-FREE bounds.
  Two nested Euclidean bumps `χ ⊆ {χ₁=1} ⊆ source`; `Bχ` from `bddAbove_image` of
  `(continuous_iteratedFDeriv).norm` on compact `tsupport χ`; `Bg` from
  `metricComp_iteratedFDeriv_le` on `Kc := (extChartAt x₀).symm '' tsupport χ`,
  pulled back through the χ₁=1 germ (`χ₁` =1 on a nbhd of `tsupport χ` ⇒
  `∇ʳ(χ₁·chartRep) = ∇ʳ chartRep` there); assembled by `norm_iteratedFDeriv_bumpMul_le`.
- `exists_chart_cInfConv (…) : ∃ (φ : ℕ→ℕ) (Φinf : E→ℝ) (χ : E→ℝ), StrictMono φ ∧
  ContDiff ⊤ Φinf ∧ (∀y∈K₀, χ(extChartAt y)=1) ∧ MapCInfConvOnCompacts univ
  (fun k => χ · chartRep(gSeq (φ k))) Φinf` — **the stated endpoint** (per-chart
  subsequence + C^∞ limit component).  Applies `exists_cInf_subseq Φ hΦcd (fun r K
  _ => …)` (the `hbdd` ignores K and uses the K-free `∀r,∃M` bound), then bridges
  `fun k => Φ(φ k)` back to `fun k => χ·chartRep(gSeq(φ k))` by `(hΦrel (φ k)).symm`.

Producer gotcha: `rw [hΦeq]` fails (target `(fun k x => …) k` not β-reduced) ⇒
use `simp only [hΦeq]`.

### REMAINING (atlas × component diagonal — NOT done; couples to Brick C)

`exists_chart_cInfConv` gives ONE subsequence per (chart, component) pair.  The
full Corollary needs ONE subsequence working for ALL charts of a σ-compact
countable atlas × all n² covariant components simultaneously.  Scoped 2026-06-11:
this is genuinely **two frontiers, coupled to Brick C** — flag to planner, do NOT
bolt onto Brick B in a vacuum.

**Frontier 1 — abstract countable common-subsequence diagonal (NOT in Mathlib).**
`DiagonalSubseq.exists_subseq_tendsto_pi` uses product-compactness, which needs
COMPACT metrizable fibers (`Icc`, `Bool`); C^∞ limits are not in a compact fiber,
so it does NOT apply.  Mathlib has only `Filter.extraction_forall_of_frequently`
(`{P : ℕ→ℕ→Prop} (∀n, ∃ᶠ k, P n k) → ∃ φ, StrictMono φ ∧ ∀ n, P n (φ n)` —
`Mathlib/Order/Filter/AtTopBot/Basic.lean:144`), the `∀n, P n (φ n)` diagonal
*building block*, NOT the "one subsequence along which countably many
subseq-stable properties ALL hold."  Hand-roll: nested extractions
`G 0 = id`, `G (n+1) = G n ∘ ρₙ` (ρₙ = extractor for item n along `G n`),
diagonal `φ n := (G (n+1)).1 n`.  `StrictMono φ` is clean (`ρₙ k ≥ k` +
`G(n+1)` strict mono).  The friction: `P i φ` needs `φ`-tail = `(G(i+1)).1 ∘ σ`
(σ strict mono) — a SHIFT, not eventual-equality — so the abstract lemma needs a
P-stability hypothesis covering tail-subsequence/shift (`hsub` + shift-invariance,
or expose the witness `ψ_i=(G(i+1)).1` + relation in the conclusion and let the
instantiation discharge stability).  EXACT hypothesis shape is determined by Brick
C's convergence formulation (`MetricCInfConvOnCompacts` is tail+subseq invariant
via `MapCInfConvOnCompacts.comp_subseq` (MapConvergence.lean:103) and the
asymptotic `∃k₀` in `MapCPConvOn`) — so build the lemma WITH Brick C, not before.

**Frontier 2 — σ-compact countable atlas / compact exhaustion (Mathlib API not yet
located).** Enumerate `(chartₙ, component_ab)` over a countable atlas (need a
`SigmaCompactSpace`/`SecondCountableTopology` cover-by-charts lemma — CHECK
Mathlib manifold API), run `exists_chart_cInfConv` per item as the Frontier-1
extractor, then assemble `MetricCInfConvOnCompacts` over a compact exhaustion
`M = ⋃ Kₙ`.  This assembly IS Brick C's C1 (global limit object `gInf`) — the
diagonal and the limit-object construction are one design unit (`metricPreconvInf`
endpoint, P3_PLAN §Brick C).  Recommendation: implement the diagonal as the
opening of Brick C, reusing `exists_chart_cInfConv` as the per-item extractor.

## Brick B foundation (generic Euclidean, verified green, producer-ready)
- `bumpMul_contDiff` — `χ` (smooth bump, `tsupport ⊆ U` open) `× g` (`ContDiffOn U`)
  is globally `ContDiff ⊤` on `E`.
- `norm_iteratedFDeriv_bumpMul_le` — `‖∇ʳ(χ·gg)‖ ≤ 2ʳ·Bχ·Bg` EVERYWHERE, given
  `χ`/`gg` derivative bounds `Bχ`/`Bg` on `tsupport χ` for orders `≤ r` (off
  `tsupport χ` the χ-derivatives vanish ⇒ the product derivative does).
  `K`-independent — exactly `exists_cInf_subseq`'s `hbdd` shape.  (Hyps are
  `∀ i ≤ r`, not `∀ i`: a fixed smooth function's high-order derivatives grow, so
  the metric supplies `Bg = max_{j≤r}` of the A2 bounds.)

**A2 constants-first FIX (necessary for Brick B, committed):**
`iteratedFDeriv_comp_le_tower` was restated `∃ CV, 0 ≤ CV ∧ ∀ A0, …` (A0 moved
INSIDE the ∀, after `∃CV`) instead of taking `A0` as an outer parameter.  With
`A0` outer, `(A2 … (metricTensorField (gSeq k)) …).choose` is an opaque
k-dependent value — `exists_cInf_subseq` needs a k-INDEPENDENT bound.  A2's `CV`
is genuinely `A0`-independent (base `D^(p+2)`, step preserves), so the restated
form exposes the single uniform `CV`.  Proof unchanged except `intro A0` +
threading `A0` through the `hCfb`/`hCcb` IH constants.  **Any future
`iteratedFDeriv_comp_le_tower` call must apply `CV` first, then `∀ A0`.**

Route for the metric producer (next): two nested Euclidean bumps `χ ⊆ {χ₁=1} ⊆
target` (via `exists_contMDiffMap_one_nhds_of_subset_interior` at model
`𝓘(ℝ,E)` + `contMDiff_iff_contDiff`); `g̃_k := χ₁·(chart rep of the (i,j)-component
of gSeq k)` global (`bumpMul_contDiff`); `Φ_k := χ·g̃_k`; `Bg` from A2
(`iteratedFDeriv_comp_le_tower` at p=0, A0=`metricTensorField (gSeq k)`,
V=globalized chart-const frame) — the A2 `b q` = `metricCovDerivNorm q (gSeq k)
gRef z` (`metricCovDeriv_eq_covDerivOfField`), bounded uniformly in k by the
`(B_r)` hypothesis (`MetricCovDerivOrderBoundOn`); `g̃_k = chart rep` germ on
`tsupport χ` (χ₁=1 there) so `∇ʳ g̃_k = ∇ʳ chartRep`.  Then `exists_cInf_subseq`
per chart/component + σ-compact atlas × n² diagonal.  Gotcha: `g̃` (combining
tilde) is NOT a valid Lean identifier — use `gg`.

**Status: Bricks A1 + A2 IMPLEMENTED, verified (focused+targeted build green,
#print axioms clean) (2026-06-11).**

## Brick A2 DONE — `iteratedFDeriv_comp_le_tower` (MetricPreconv.lean)

The all-orders covariant→coordinate conversion is proved sorry-free.  For every
order `r`, level `p`, and `∞`-section tuple `V`:
`‖iteratedFDeriv ℝ r (chart rep of s_p^V) (extChartAt y)‖ ≤ CV · Σ_{q≤p+r} b q`
on an inner compact `Kc`, `CV` = gRef/chart/slot/basis data only (A0-independent
⇒ k-independent on a metric sequence).  This is exactly what `exists_cInf_subseq`
(MapConvergence) needs as its per-order `hbdd` (Brick B feeds it after a fixed
bump-Leibniz and the P2 (B_r) uniform bounds).

New public exports (reusable by B/C/D):
- `iteratedFDeriv_comp_le_tower` — the endpoint.
- `clm_eq_sum_coord` — `L = Σ_i (L bEᵢ)·coordᵢ` (function-level CLM basis identity).
- `extDerivFun_tower_step` — pointwise tower step decomposition (the A1 `hdecomp`
  extracted, for every `q`).
- `towerStep` (def) — the directional step scalar; `fderiv_chartRep_eq_towerStep`
  — the germ `fun z'↦ fderiv F z' v =ᶠ[𝓝 z] writtenInExtChartAt (towerStep)`.
- `contDiffAt_chartRep` — chart-rep `ContDiff` from `ContMDiff`
  (`contMDiffOn_extChartAt_symm` + `contMDiffOn_iff_contDiffOn`).
- `writtenInExtChartAt_real_apply` — `writtenInExtChartAt 𝓘(ℝ,ℝ) g z = g (symm z)`.
- `covDerivOfField_eval_contMDiff` — full `ContMDiff` of a tower scalar.
- `iteratedFDeriv_smul_const_le` — `‖∇ʳ(g•c)‖ ≤ ‖c‖·‖∇ʳg‖`.
- `exists_section_eqOn_compact` STRENGTHENED to the `∀ᶠ x in 𝓝ˢ Kc` form (A1's
  single use updated to `(hσ i).self_of_nhdsSet y hy`).

### Route

Induct on `r` (`generalizing p V`, so the IH is `∀ p V`).  Base `r=0`:
`‖∇⁰F z‖ = |s_p^V y|`, Cauchy–Schwarz (as A1's base).  Step `r→r+1`:
`‖∇^{r+1}F z‖ = ‖∇ʳ(fderiv F) z‖` (`norm_iteratedFDeriv_fderiv`); the germ
`fderiv F =ᶠ Σ_i (chart rep towerStep_i)·coordᵢ` (combine `clm_eq_sum_coord`
pointwise with the per-direction `fderiv_chartRep_eq_towerStep`); push `∇ʳ`
through the finite sum + the scalar·const-covector (`iteratedFDeriv_fun_sum_apply`
+ `iteratedFDeriv_smul_const_le`); split each `writtenInExtChartAt towerStep_i`
into the level-`(p+1)` scalar (tuple `Fin.cons σᵢ V`) + Σ level-`p` scalars
(tuples `update V a (∇_{σᵢ}Vₐ)`) and apply the IH.  Order bookkeeping:
`{p..p+r}` at level p and `{p+1..p+1+r}` at level p+1 union to `{p..p+r+1}`.

### Lean gotchas (A2-specific; for B/C/D)

- **Section-tuple coercion**: `(Fin.cons (σ i) V) a w` / `(Function.update V a
  (W i a)) bb w` do NOT resolve the `ContMDiffSection` `CoeFun` inline ("Function
  expected") — the `Fin.cons`/`update` motive is a metavar.  Fix: bind a typed
  `let Vf : Fin m → Fin (p+3) → ContMDiffSection … := fun i => Fin.cons (σ i) V`
  (and `Vc` for the updates), then `Vf i a w` coerces fine.  Let the IH instances
  (`ih (p+1) (Vf i)`) INFER the bound statement (don't hand-write the `∃`).
- `@[to_fun]` PREPENDS `fun_`: the function-form add lemma is
  `fun_iteratedFDeriv_add_apply` (not `iteratedFDeriv_fun_add_apply`).
- `Filter.EventuallyEq.iteratedFDeriv` takes `𝕜` EXPLICIT (`variable (𝕜) in`):
  `hgerm.iteratedFDeriv Real r`.
- Order-`r` `iteratedFDeriv` linearity lemmas want `ContDiffAt ℝ r`; the chart
  reps are `ContDiffAt ℝ ∞` → `.of_le hr` with `hr : (r:WithTop ℕ∞) ≤ ∞ :=
  by exact_mod_cast le_top`.
- `rw [iteratedFDeriv_fun_sum_apply …]` over a `g•const` summand fails to match
  (the `.smul` hypothesis is Pi-smul `f•g`, the target is explicit `fun z'↦ f z'•c`)
  — pass `(f := fun i z' => … z' • c i)` explicitly so the rw pattern is the
  explicit form (the Pi-smul ContDiffAt is accepted by defeq).
- `Finset.range_subset.2` would not apply to give the subset from `m ≤ n` here;
  prove `range m ⊆ range n` directly via `mem_range`.
- separate `omega` goals from `Finset.range_subset`/`congr` (`omega` saw
  abstracted vars otherwise).

## Brick A1 DONE — `fderiv_comp_le_tower` (MetricPreconv.lean)

**Status: Brick A1 IMPLEMENTED + read-only verified (2026-06-11).**

## Brick A1 DONE — `fderiv_comp_le_tower` (MetricPreconv.lean)

The order-1 covariant→coordinate conversion is proved sorry-free.  File
`HCGCompactness/MetricPreconv.lean` exports (all public, reused by A2/B):

- `fderiv_comp_le_tower` — the endpoint.  `‖fderiv (chart rep of s_p^V)‖ ≤
  CV·(Cp1+Cp)` on an inner compact `Kc ⊆ chart source`, with `CV` collecting
  gRef/chart/slot/basis data only (A0-independent — so k-independent on a metric
  SEQUENCE; the load-bearing quantifier discipline `∃CV … ∀y∀Cp,Cp1`).
- `opNorm_le_sum_coord` — generic finite-dim `‖L‖ ≤ Σ‖coordᵢ‖·|L(bEᵢ)|`.
- `exists_ON_tangentBasis` — general-dim gRef-orthonormal tangent basis at a
  point (repackages `exists_trivONBasis` via `IsLocalFrameOn.toBasisAt`).
- `exists_section_eqOn_compact` — bump-globalizes `tangentConstInChart x₀ v` to a
  genuine `ContMDiffSection` agreeing on `Kc`.
- `exists_sqrtInner_bound` / `exists_family_bound` — compact sup of the
  gRef-norm of a (family of) smooth section(s).

### Route as implemented (one simplification vs the plan)

Plan's per-slot product bookkeeping was replaced by a **uniform bound `D`**: one
constant bounding `√gRef(s·,s·)` on `Kc` for every direction `σ i`, slot `V a`,
and correction `W i a = ∇_{σ i}(V a)`.  Then each Cauchy–Schwarz slot product is
`≤ D^(p+3)` / `≤ D^(p+2)`, so `|fderiv·(bEᵢ)| ≤ Cp1·D^(p+3)+(p+2)·Cp·D^(p+2)`,
and `opNorm_le_sum_coord` + `CV := max(Ccoord·D^(p+3), Ccoord·(p+2)·D^(p+2))`
closes it.  Crude constant, but k-independent and far less bookkeeping.

Otherwise as scouted: chart bridge `extDerivFun_tangentConstInChart_eq_fderiv`
(per-direction), step decomposition `covDerivOfField_succ` +
`metricCovDerivStep_apply` + `totalNabla0SFun_apply_section` +
`nabla0SFun_eval_smooth_slots` (no `Fin.cons` `hv`/`hupd` needed — the cons is
formed directly), CS `abs_apply_le_sqrt_normSq0S`.

### Lean gotchas hit (record for A2/B)

- `metricInner_mdiffAt` and `cotangentCov_pairing_contMDiff` carry an
  `[InnerProductSpace ℝ E]` section var the HCG block lacks → **inline** the
  `g.contMDiff` + `ContMDiff.clm_bundle_apply` (×2) + `contMDiffAt_section`
  chain instead (no inner product needed; that var is unused in their proofs).
- Bump `exists_contMDiffMap_one_nhds_of_subset_interior` wants `n : ℕ∞`; pass
  `(⊤ : ℕ∞)` so `χ.contMDiff` lands at `(∞ : WithTop ℕ∞)` matching the section.
- `NormalSpace M` is not directly inferred: add
  `LocallyCompactSpace H := I.locallyCompactSpace`,
  `LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M`, then
  `NormalSpace M := inferInstance` (PouThickening pattern).
- `abs_add` → `abs_add_le`.
- `Fin.cons x f a` inside `gRef.inner y (…)` cannot infer its motive → ascribe
  `(Fin.cons … : Fin (p+3) → TangentSpace I y)`.
- `Finset.prod_le_prod` cannot infer the upper-bound function `g` under
  `le_trans` → pass `(g := fun _ => D)` and finish with `le_of_eq`.
- `Function.update_of_ne` (not `update_noteq`); `Function.update_self`.

**Status: PLAN below (the rest, Bricks A2/B/C/D, 2026-06-11). Brick A1 done.**

## Where this sits

P3 of the Lemma 3.11/Theorem 3.10 chain (and a SHARED engine: the Ch4
Thm 3.9 (`metricCompactness`) proof cites the same corollary).  Book source:
MSM135 ch3, Corollary `lbl351` (proof sketch at lines ~788-813 of
`RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter3.tex`), consumed by
the Thm 3.10 assembly (`lbl352` subsection).

## Statement (target form, C^∞/global version — what both consumers want)

```
theorem metricPreconvInf
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ α : ℕ, ∀ K, IsCompact K → ∃ C, ∀ k,
      MetricCovDerivOrderBoundOn (I := I) K α (gSeq k) gRef C)
    (hlow : ∀ K, IsCompact K → ∃ δ > 0, ∀ k, ∀ x ∈ K, ∀ v,
      δ * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf gRef
```

(The per-`p`, per-`K` book statement lbl351 is the engine inside; the
diagonal over a countable chart cover + orders gives the global C^∞ form,
which is what `MetricCInfConvData` / the 3.10 assembly and Thm 3.9 need.
The lower bound makes the limit positive-definite.)

## Deviation from the book recorded (3.10 application)

The book gets SPACETIME C^∞ convergence by applying lbl351 to `g∞ + dt²` on
`M × (α,ω)` — which needs the FULL mixed `(p,q)` bounds of Lemma 3.11
(lbl341, q ≥ 1, via the curvature evolution equation).  The project's
consumer (`SourceMetricCPConvOnWindow`, PointedConvergence.lean:777) only
requires SPATIAL C^p sup-norms uniformly in t — so P3 takes the lighter
route: per-t spatial preconvergence (this file) + time-equicontinuity from
the q = 1 bound only (`∂ₜ∇ᵖg = -2∇ᵖRc`, bounded by `ric_bound` + (B_r) —
all P2 machinery, NO curvature-evolution recursion needed).  The q ≥ 1
mixed bounds of lbl341 are NOT formalized (not consumed).

## Proof route (per book sketch + project reuse)

1. **Componentize** on a countable atlas: in a chart, the scalar components
   `(g_k)_{bc}(y)` (coordinate frame / `extChartAt`-pullback to an open ball
   of ℝⁿ).
2. **Covariant→coordinate derivative conversion** (the genuinely new layer):
   `∇^α_gRef`-bounds (α ≤ A) ⇒ chart-component `iteratedFDeriv` bounds
   (orders ≤ A) on compact sub-balls.  Induction:
   `∂(comp) = ∇-comp + Γ·comp` (book lbl345-form); gRef's Christoffel +
   derivatives bounded on compacts (smooth fixed background).  REUSE
   candidates: `AkMFold.iterCovCompU` / `covDerivStepCompU` (component
   covariant tower = ∂-step − chr-corrections; invert the recursion),
   `Claim1Wiring` producers (lcChrist_e_mdiffOn etc.),
   `Geometry/Coordinates/NablaComponents/`.
3. **Euclidean engine**: bump-extend the components from a compact sub-ball
   to all of ℝⁿ and feed `exists_cInf_subseq` (MapConvergence.lean — the
   other session's sorry-free AA-diagonal engine; E := ℝⁿ, F := ℝ); OR add
   an On-version of the engine.  Output: subsequence + C^∞ limit components
   + C^∞_loc convergence per chart.
4. **Diagonal** over (countable charts) × (n² components) → one subsequence;
   reassemble the limit tensor field; positive-definiteness from `hlow`;
   smoothness of the limit from the engine's `ContDiff ⊤` output.
5. **Norm bridge**: chart-component C^p convergence ⇒ the project's
   `metricDerivNorm`-form `MetricCPConvOn` (the two-sided component↔normSq0S
   bounds of `RicBoundGoodFrame` / `Comparison.lean` — already built for
   ric_bound — convert sup-component differences to `normSq0S` differences
   of `metricDiffCovDerivAt`; this also needs the covariant tower of the
   DIFFERENCE, i.e. linearity `covDerivOfField` of `g_k − g∞`:
   `metricCovDeriv` is linear in the field (`MetricCovDerivLinear`)).

## Brick order

- **Brick A** (conversion layer, step 2): coordinate-partial bounds from
  covariant bounds.  Self-contained; sizeable.
- **Brick B** (steps 3-4): chart-local extraction + diagonal; mostly plumbing
  around `exists_cInf_subseq` + the scalar AA file.
- **Brick C** (step 5): norm-form bridge back to `MetricCPConvOn`.
- **Brick D** (time direction, separate file): window-uniform upgrade via
  q = 1 equicontinuity (consumes P2's `hevComp_of_solutions` + `ric_bound`).

## Brick A refined design (scouted 2026-06-11)

The single-step coordinate↔covariant bridge exists but only at chart CENTERS
(`covariantDerivative_modelInChart_center_eq_fderiv_plus_connection`,
`Geometry/Coordinates/NablaComponents/Tensor0S.lean:185`) — not directly
iterable over a ball.  The iterable decomposition is instead the one ALREADY
USED by the P2 tower-regularity inductions
(`MetricCovDerivTimeDeriv.lean`, `covDerivOfField_eval_smoothAt`):

  `extDerivFun (s_p^{V-tail}) (V 0) = s_{p+1}^V + Σ_a s_p^{update_a V}`
  (from `totalNabla0SFun_apply_section` + `nabla0SFun_eval_smooth_slots`),

where `s_p^V(y) := (covDerivOfField gRef A0 p) y (V·y)` and the updated slots
insert `∇_{V0}(V a)` (smooth sections; for coordinate-frame slots these are
Christoffel combinations of the FIXED gRef — bounded with all derivatives on
compacts).  So the directional derivative of the level-p scalar along any
smooth field is (level-(p+1) scalar) − (level-p scalars at modified tuples).

Induction invariant for Brick A: P(m): for every p and every slot tuple from
a fixed finite family closed under the Christoffel updates, the m-th chart
`iteratedFDeriv` of `s_p` is bounded by C⁰ bounds of `{s_q : q ≤ p + m}` at
(finitely many) tuples + chart-frame/Christoffel data.  Then `hbdd` at orders
≤ A gives chart-component `iteratedFDeriv` bounds at orders ≤ A.
Technical care: closing the slot-tuple family under updates (the update
inserts `∇_{V0} V_a`, not a coordinate frame element — either prove tuples
stay in the span with bounded coefficients (multilinearity expands them), or
phrase P(m) for ALL ∞-section tuples with bounds depending on the tuples'
own C^m data on K — the latter is cleaner: the bound constant is a function
of `sup_K ‖iteratedFDeriv^{≤m}(slot coords)‖`).

C⁰ bounds of `s_q` from `hbdd`: `|s_q(y)| ≤ ‖∇^q g_k‖_{gRef}(y) · Π‖V_a‖` —
Cauchy-Schwarz for `normSq0S` against slot vectors (exists in the
Tensor0SRiemannian layer / `Comparison.lean` two-sided machinery).

## Design decision: Euclidean engine vs equicontinuity-only (2026-06-11)

Considered and REJECTED: skipping the iteratedFDeriv conversion by proving
manifold-level equicontinuity directly (directional-derivative bounds from the
step decomposition + CS lemma give C¹ bounds per order; "C¹ bound ⇒ Lipschitz
on compacts" needs only one chart/MVT lemma) and using the scalar AA per order
+ diagonal.  REJECTED because the limit's smoothness and the
derivative↔limit interchange (`L_p = ∇ᵖ(g∞)`) would then have to be proved by
hand on the manifold tower — strictly worse than the iteratedFDeriv
conversion, which is finite-dimensional scalar calculus and after which
`exists_cInf_subseq` delivers the smooth limit + all interchanges for free.
Stick with Brick A as planned.

Brick A progress: first lemma DONE (commit e4e8db5a) —
`Tensor0SBundle.abs_apply_le_sqrt_normSq0S` (Comparison.lean): pointwise
tensor Cauchy–Schwarz `|T(v)| ≤ √normSq0S(T)·∏√g(vₐ,vₐ)` at a g-ON basis.
Proof pattern: `T.map_sum` + `T.map_smul_univ` basis expansion, discrete CS
`Finset.sum_mul_sq_le_sq_mul_sq`, slot Parseval (simp with `map_sum, map_smul,
ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_apply, hON` + `sum_comm`
+ `sum_ite_eq`), `Finset.prod_univ_sum`, private `sqrt_prod`.

## Brick A base bridges (located, 2026-06-11)

- `extDerivFun_real_eq_mfderiv` (Bundle/PartialMfderiv/FixedBase.lean:22) and
  `extDerivFun_eq_fderiv` (FixedBase.lean:199, the chart-fderiv form used by
  the swap constructors) — the scalar directional-derivative ↔ chart-partial
  bridges for the conversion induction.
- Step decomposition: `totalNabla0SFun_apply_section` +
  `nabla0SFun_eval_smooth_slots` (the P2 tower-regularity pattern in
  `MetricCovDerivTimeDeriv.lean`).
- C⁰ input: `abs_apply_le_sqrt_normSq0S` (Comparison.lean, e4e8db5a).
- Euclidean endgame: `exists_cInf_subseq` (MapConvergence.lean).

NEXT concrete step: create `MetricPreconv.lean`; first theorem = the
order-1 conversion (chart-partials of the component scalars bounded by
`(B_{p+1})`, `(B_p)` + chart-frame data via the step decomposition + CS),
then the iteratedFDeriv induction.

Order-1 route in detail:
- THE pointwise bridge is `extDerivFun_tangentConstInChart_eq_fderiv`
  (FixedBase.lean:69): for EVERY `p` in the chart source (not only the
  center), `fderiv ℝ (writtenInExtChartAt I 𝓘 x₀ f) (extChartAt x₀ p) v =
  extDerivFun f p (tangentConstInChart x₀ v p)`.
- So `‖fderiv F z‖ ≤ sup over a basis of v's` of `|extDerivFun (s_p^V)
  along the chart-constant field|`, and the step decomposition + the CS
  lemma bound that by `(B_{p+1})`/`(B_p)` times `gRef`-norms of the slot
  fields and the chart-constant direction field on the compact — finite
  sup of continuous functions.
- ⚠ SLOT GLOBALIZATION: the step decomposition (`nabla0SFun_eval_smooth_slots`)
  takes GLOBAL `ContMDiffSection` slots, but `tangentConstInChart` fields are
  only chart-smooth.  Globalize by bump-truncation (the
  `SmoothSectionsLocal.lean` bump pattern: `SmoothBumpFunction` supported in
  the chart, = 1 on the inner compact); on the inner set the truncated
  section agrees with the chart-constant field, and `extDerivFun` only
  depends on the germ (`extDerivFun_congr_nhds`).
- Higher orders: iterate `fderiv` of the chart representative; each step
  re-enters the same family `s_q` at slot tuples extended by bump-globalized
  chart-constant fields and Christoffel-update fields — the bound constants
  pick up sup-norms of those fields' derivatives on the inner compact
  (finite, gRef/chart data only, k-independent ✓).

## Open design questions

- Whether to add an `On`-version of `exists_cInf_subseq` vs bump-extension
  (bump route keeps the other session's file untouched — preferred while
  they are active in MapConvergence.lean's neighborhood).
- The limit's global assembly: chart-local C^∞ limits glue by uniqueness of
  limits (overlaps agree pointwise); the global smooth metric is built chart
  by chart — check whether `SmoothRiemannianMetric` has a local-construction
  constructor or whether to build the `(0,2)`-field first and add
  positivity/symmetry.

## 2026-07-09: per-order reference adapter

Added `metricComp_iter_refs`. For chart derivative order `r`, it accepts uniform covariant bounds
only through order `r` against `gRef r`. The older all-orders conversion theorem formally asks for
all covariant orders, so orders above `r` are filled using compact boundedness for each fixed
sequence term; those constants do not enter the finite sum in the conclusion. Focused
verification passed. This is the D2 prefix-tail bridge that avoids a new global
connection-change estimate while preserving the existing fixed-reference API.

## 2026-07-14: fixed-order family and chart-Gram bounds

Added and focused-verified `metricComp_iter_le`, `chartGram_germ`,
`chartGram_iter_le`, and `chartGram_of_orders`.

`metricComp_iter_le` accepts an arbitrary metric family indexed by any type and
requires family-uniform covariant bounds only for orders `q <= r`.  The old
all-orders tower theorem formally asks for a bound at every order; orders above
`r` are supplied separately for each fixed smooth metric by compact
boundedness, and those values do not occur in the finite sum defining the
uniform constant.  The old sequence-facing theorem is now a compatibility
specialization.

`chartGram_germ` identifies globalized chart-basis component germs with
`chartGramOnE`.  The two chart-Gram theorems then turn exact-order predicates
`MetricCovDerivOrderBoundOn K q ... B`, through order `r`, into one uniform
bound for every order-`r` `iteratedFDeriv` of every Gram entry on a compact
chart piece.  At `r = 3`, this closes the intrinsic-C3 to chart-C3 coefficient
bridge needed as input to a low-regularity Ricci--DeTurck theorem.

`chartGram_pou_le` further aggregates these bounds over the canonical finite
`chartAtlasPOU_finset`, producing one fixed-order constant for every active
chart support, family member, and Gram entry.  Focused verification passes.

This is coefficient infrastructure, not parabolic existence.  The uniform
low-regularity Ricci--DeTurck theorem remains 0%.  After the later
`LowRegCoeff` assembly, dedicated E1 machinery is about 28%, with the actual
low-regularity solver and uniform smoothing interval still missing.

## 2026-07-14: active-chart partial bounds through order three

Added `chartGram_pou_bnd`, `chartGram_pou_d1`, `chartGram_pou_d2`, and
`chartGram_pou_d3`.  They specialize the fixed-order `iteratedFDeriv` estimate
to absolute coordinate Gram bounds of orders zero through three on every
active partition-of-unity chart support.  The first three orders feed the full
Ricci--DeTurck `2`-jet Lipschitz estimate; order three is retained as the
coefficient-regularity input for the future low-regularity parabolic solver.

Focused verification passed.  These are constants-first family producers and
do not assert existence or regularization of a flow.

## 2026-07-17: pointwise chart-jet difference bridge

Added and focused-verified `iterFDeriv_tower_le` and `chartJet_sub_le`.
The former exposes the pointwise estimate already proved by the all-orders
tower induction: compactness controls only the chart/slot constant, while the
covariant tensor norms on the right are evaluated at the current point.  The
existing constants-first `iteratedFDeriv_comp_le_tower` statement is unchanged
and is now a compatibility corollary, so its downstream consumers require no
new hypotheses or edits.

`chartJet_sub_le` applies the pointwise tower to
`metricTensorField u - metricTensorField u'` before taking norms.  Linearity of
`covDerivOfField`, the chart-Gram germ, and `iteratedFDeriv_sub_apply` then give
one compact-dependent constant controlling every order-`r` Gram-jet difference
by the sum of `metricDerivNorm` through order `r`.  This closes the spatial
covariant-to-chart convergence bridge needed for `ConvOut.gramJets`; it does
not itself prove the fixed-window `ConvOut.gramSmooth` theorem, which remains
0%.  The dedicated P4 regularity machinery is still approximately 88--89%; the
time-slice swap and finite jet-algebra bootstrap remain independent frontiers.

The same bridge now also exports `chartJet2_sub_le`.  It first packages each
matrix-valued derivative order through the nested finite-Pi norm, then uses the
canonical calculus lemma `Analysis.jet2_sub_le` to control the complete
value/first/second-derivative jet.  The statement adds no hypothesis to
`ConvOut` and focused verification plus the targeted module refresh passed.
