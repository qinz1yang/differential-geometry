# MetricPreconvDiag.lean — P3 Brick C-I (countable diagonal + global limit)

**Status (2026-06-12): C0 + C1a + C1b ALL DONE + verified (focused check +
targeted build green 3848 jobs; `#print axioms metricPreconv_gInf` clean =
`[propext, Classical.choice, Quot.sound]`).  The Brick C-G bridge
`smoothMetric_of_localCoeff` unblocked C1a/C1b; endpoint
`metricPreconv_gInf` constructs the limit `SmoothRiemannianMetric`.
(2026-06-13) C-II-final-B0 added: `exists_engine_frameCInfConv` +
`exists_engine_frameCInfConv_eq_gm` re-expose the engine's `C^∞`-on-compacts
frame-component convergence (Gap A); both axiom-clean, `metricPreconv_gInf`
unchanged.  (2026-06-13) C-II-final-B1: `componentConv_covDeriv_zero` proves the
covariant-tower bridge at order `a = 0` (base case, axiom-clean).  The two
original `a ≥ 1` missing pieces are now DONE: derivative-closure of
`MapCInfConvOnCompacts` (`MapConvergenceDeriv.lean`) and the rank-general
coordinate/tower covariant-step formulas (`CoordFrameStep.lean`,
`MetricCovDerivCoordStep.lean`).  The `C∞` convergence induction assembly is now
proved by `bumpTowerCarrier_all`; frame data is proved by `exists_frameData`;
and the order-0 base algebraic reduction is proved by `hbase_of_framePairs`.
Remaining work is the B0 diagonal to `hpairs`, pointwise extraction,
finite-cover `hnorm`, and `metricPreconvInf`.  See "Gap A exposed" / "Gap B base
case" / "Gap B remaining" below.**

## C1a + C1b DONE (2026-06-12) — verified lemma inventory

Endpoint `metricPreconv_gInf (hne : Nonempty M) gRef gSeq (hbdd : (B_r)) (hlow :
∃ c>0, ∀ k x v, c·gRef ≤ gSeq k) : ∃ φ, StrictMono φ ∧ ∃ gInf :
SmoothRiemannianMetric I M, ∀ x, Tendsto (fun m => (gSeq (φ m)).inner x) atTop
(𝓝 (gInf.inner x))`.  The chain (all axiom-clean):

- `frameVec_eq_tangentConst` — `Geometry.frameVec x₀ i = tangentConstInChart x₀
  (Module.finBasis ℝ E i)` by `rfl` (the make-or-break seam; privacy of `mdlBasis`
  is bypassed by defeq to the public `finBasis`).
- `exists_tendsto_clm_of_basis_eval` — finite-dim: a bilinear-form sequence
  converges (to SOME limit) if every basis-pair matrix entry converges
  (`LinearMap.isClosedEmbedding_of_injective` of the eval map +
  `IsClosed.mem_of_tendsto`).  REUSABLE (Thm 3.9 too).
- `exists_chart_cover` (C1a) — σ-compact ⇒ countable `(c k, K k)` with `K k`
  compact ⊆ chart source, covering `M` (`exists_compact_subset` + Lindelöf
  `elim_countable_subcover` + `Set.Countable.exists_eq_range`).
- `exists_gm_symm_pos` — from pointwise convergence `hconv` + `hlow`: the limits
  `gm := (hconv x).choose` are symmetric (each term is; `tendsto_nhds_unique`) and
  positive-definite (`ge_of_tendsto` of `c·gRef ≤ gSeq k`, `gRef.pos`).
- `exists_engine_frameConv` — engine consumption WITH the smooth limit: run
  `exists_chart_cInfConv` on `gSeq ∘ φ` at `x₀` with `![σi, σj]` = globalized
  `frameVec` (via `exists_section_eqOn_compact` at `finBasis i,j`); on `K₀` the
  converged scalar is `(gSeq …).inner x (frameVec i x)(frameVec j x) → Φinf
  (extChartAt x)`, `Φinf` `ContDiff ∞`.  `exists_refine_componentConv` is the
  forget-`Φinf` corollary (the diagonal `hstep`).
- `exists_frameVec_basis` — `frameVec x₀ · x` is a `Basis` of `T_x M` for `x ∈
  baseSet` (`(finBasis).map (continuousLinearEquivAt x hx).symm`; `symmL = symm`
  by `rfl`).
- `exists_refine_allComponents` — finite fold of `exists_refine_componentConv`
  over the `n²` pairs (`Finset.induction`; earlier pairs survive by
  subsequence-stability).
- `exists_limit_gm` — diagonal (C0) over the cover with `hstep =
  exists_refine_allComponents`, `hsub`/`hextend` from convergence
  subsequence/tail-stability; at each `x` combine the `n²` scalar limits into a
  CLM limit (`exists_frameVec_basis` + `exists_tendsto_clm_of_basis_eval`) ⇒
  `hconv`; then `exists_gm_symm_pos`.
- `frameComp_contMDiffOn` (`hcoeff`) — per `x₀`, frame component smooth on
  `baseSet`: locally near `z`, `exists_engine_frameConv` gives `Φinf`; the
  component `= Φinf ∘ extChartAt` on `K₀` by `tendsto_nhds_unique` (gm = lim along
  φ; same along φ∘ψ), smooth by `contMDiffAt_extChartAt'` +
  `contMDiff_iff_contDiff`, lifted to `ContMDiffOn baseSet` via
  `ContMDiffAt.congr_of_eventuallyEq` on a compact nbhd.
- `metricPreconv_gInf` — assemble via `Geometry.smoothMetric_of_localCoeff gm
  hsymm hpos hcoeff`; `gInf.inner = gm` ⇒ the pointwise `Tendsto` endpoint.

### Lean gotchas (C1a/C1b)
- `L∞` is NOT a valid identifier (`∞` is a notation token) → `Linf`.
- `exists_chart_cover`/`frameComp_contMDiffOn` need `haveI : LocallyCompactSpace
  H := I.locallyCompactSpace; … M := ChartedSpace.locallyCompactSpace H M`, and
  `include I in` (the cover statement does not mention `I`, so the section var is
  otherwise dropped).
- `Filter.Eventually.self_of_nhdsSet` takes the point EXPLICITLY (`hσ.self_of_nhdsSet x hx`).
- `[InnerProductSpace ℝ E]` on the model (the bridge's requirement, for
  `posDef_isVonNBounded`) — declared in the section; it extends `NormedSpace`, so
  MetricPreconv's lemmas still apply.

### Endpoint note (for C-II / planner)
`metricPreconv_gInf` delivers the POINTWISE-CLM-limit form (subsumes
chart-component convergence).  The C2 `metricDerivNorm` bridge
(`metricCInfConvOnCompacts_of_normConv`) wants uniform-on-compacts component
convergence; the engine's `MapCInfConvOnCompacts` provides it but `metricPreconv_gInf`
keeps only the pointwise extraction.

### Gap A exposed (2026-06-13, C-II-final-B0)
The engine's `C^∞`-on-compacts frame-component convergence is now re-exposed
(both axiom-clean; `metricPreconv_gInf` unchanged):

- `exists_engine_frameCInfConv (gRef gSeq) (hbdd) (x₀ {K₀} hK₀ hK₀chart) (i j) (φ)
  : ∃ ψ Φinf χ σi σj, StrictMono ψ ∧ ContDiff ∞ Φinf ∧ (σi/σj = frameVec i,j on K₀)
  ∧ (χ ∘ extChartAt = 1 on K₀) ∧ MapCInfConvOnCompacts univ (fun k x => χ x ·
  writtenInExtChartAt x₀ (fun w => (gSeq (φ (ψ k))).inner w (σi w)(σj w)) x) Φinf`.
  Same engine setup as `exists_engine_frameConv`, but returns the FULL
  `MapCInfConvOnCompacts` rather than the pointwise `Tendsto`.  The engine's raw
  `covDerivOfField gRef (metricTensorField ·) 0` chart function is rewritten to the
  clean `.inner w (σi w)(σj w)` form globally (via `covDerivOfField_zero` +
  `metricTensorField_apply`, valid for every `w`).
- `exists_engine_frameCInfConv_eq_gm (… φ gm hgm …)` — given the `gm` pointwise
  convergence (the `exists_limit_gm`/`metricPreconv_gInf` output), pins the limit:
  `∀ x ∈ K₀, Φinf (extChartAt x) = gm x (frameVec i x)(frameVec j x)` (pointwise-
  limit uniqueness, the `frameComp_contMDiffOn` route — `tendsto_nhds_unique` of the
  engine `MapCInfConvOnCompacts` pointwise extraction vs the `gm`-evaluated limit).
  So the chart components of `gSeq (φ (ψ ·))` converge `C^∞`-on-compacts to the
  chart component of the LIMIT metric `gInf` (= `gm`).

### Gap B base case DONE (2026-06-13, C-II-final-B1) — `componentConv_covDeriv_zero`
The COVARIANT order `a = 0` of `componentConv_covDeriv_of_chartCInf` is proved
(axiom-clean):
```
componentConv_covDeriv_zero (gRef gSeq) (φ) (gInf)
  (hconv : ∀ x, Tendsto (fun m => (gSeq (φ m)).inner x) atTop (𝓝 (gInf.inner x)))
  (x) (b : Basis (Fin (finrank E)) ℝ (T_xM)) (I0 : Fin 2 → Fin (finrank E)) :
  Tendsto (fun m => component0S b (metricCovDeriv (gSeq (φ m)) gRef 0 x) I0) atTop
    (𝓝 (component0S b (metricCovDeriv gInf gRef 0 x) I0))
```
`metricCovDeriv g gRef 0 = covDerivOfField gRef (metricTensorField g) 0 =
metricTensorField g` (`covDerivOfField_zero`), so `component0S b (·) I0 =
g.inner x (b (I0 0))(b (I0 1))` (`component0S_apply` + `metricTensorField_apply`);
convergence is then the limit-metric CLM convergence `hconv` (= `metricPreconv_gInf`
output) under continuous evaluation `η ↦ η (b (I0 0))(b (I0 1))`.  This is frame-
GENERAL (any fibre `Basis b` — so it serves the good-frame `toBasisAt` the norm
bridge uses), and needs only the CLM convergence, NOT the `C^∞` (chartCInf) input.
With the norm bridge at `a = 0` it gives `metricDerivNorm 0 (gSeq k) gInf gRef → 0`
(the order-0 slice of `hnorm`).

### Gap B remaining (`a ≥ 1`) — both original "missing pieces" now DONE (2026-06-13)
The two pieces that previously blocked this are both resolved:

1. **(analytic) `C^∞`-on-compacts ⇒ derivative convergence — DONE (B2).**
   `MapCInfConvOnCompacts.fderivApply` (`MapConvergenceDeriv.lean`):
   `MapCInfConvOnCompacts U Φ Φinf → MapCInfConvOnCompacts U (fun k z => fderiv ℝ
   (Φ k) z v) (fun z => fderiv ℝ Φinf z v)`.  Plus producer (3)
   `MapCInfConvOnCompacts.add/.mulLeft/.sum` (same file) for the Christoffel sums.

2. **(algebraic) rank-general coordinate covariant-derivative formula — DONE
   (producer 2).**  `Tensor.Coordinates.nabla0SFun_eval_coordFrame`
   (`Geometry/Coordinates/NablaComponents/CoordFrameStep.lean`) for arbitrary slot
   count, specialised to the metric tower by
   `metricCovDeriv_succ_component_coordFrame`
   (`HCGCompactness/MetricCovDerivCoordStep.lean`):
   `component0S (coordinateFrameAt_toBasis x) (metricCovDeriv g gRef (a+1) x) I0 =
    coordDeriv0SAt (coordinateFrameAt x (I0 0)) x (metricCovDeriv g gRef a) (tail I0)
    − Σ_p Σ_k Γ^k · coordComponent0SAt (metricCovDeriv g gRef a x) (update (tail I0) p k)`.

**REMAINING = boundary inputs to `bumpTowerCarrier_all`, then
`componentConv_covDeriv_of_chartCInf` + finite-cover `hnorm` + `metricPreconvInf`.**
The induction core itself is done in `ComponentConvTower.lean`:
- `MapCInfConvOnCompacts.congr` (locality),
- `chartRep_towerScalar_contDiffOn` / `bumpTowerScalar_contDiff` (smooth carriers),
- `bumpFderiv_eq_chartTowerStep` / `bumpTowerStep_chartConv` (directional step via
  B2 + the A2 `fderiv_chartRep_eq_towerStep` germ identity),
- `bumpTower_slotExpand_conv`, `MapCInfConvOnCompacts.sub`,
  `bumpTowerStep_split`, `bumpTowerStepScalar_contDiff`, `bumpTowerCons_conv`,
  `bumpTowerCarrier_step`, and `bumpTowerCarrier_all` (the full all-levels
  carrier induction from an order-0 base).

The remaining inputs are bounded:
- **B0 diagonal to `hpairs`**: diagonalise `exists_engine_frameCInfConv` over the
  `n²` frame pairs into one subsequence, keeping the `C∞` data and aligning
  `A0Seq k = metricTensorField (gSeq (φ k))` with the B0 bump data.
- **extract**: order-0 of the C∞ tower at the point plus a fixed multilinear
  basis-vector expansion gives the pointwise `Tendsto` matching
  `componentConv_covDeriv_zero`'s shape for general `a`; then finite-cover `hnorm`
  (`metricDerivNorm_le_compSq_uniform`) → `metricPreconvInf`.

The former `frame data` risk is resolved by `exists_frameData`, whose `hspan`
uses Mathlib's local-frame coefficient API; the former base algebraic reduction
is resolved by `hbase_of_framePairs`, which consumes the still-needed `hpairs`.

Do not add a hypothesis that simply asserts covariant-tower convergence.
`fderiv_chartRep_eq_towerStep` (MetricPreconv.lean) is the scalar-on-sections germ
form of the same step recursion (alternative to the `component0S` route above).

## C0 — `exists_diag_subseq` (DONE)

The abstract countable common-subsequence diagonal, proved exactly as the planner
fixed it:

```
exists_diag_subseq
  (P : ℕ → (ℕ → ℕ) → Prop)
  (hstep   : ∀ n φ, StrictMono φ → ∃ ψ, StrictMono ψ ∧ P n (φ ∘ ψ))
  (hsub    : ∀ n φ ψ, StrictMono ψ → P n φ → P n (φ ∘ ψ))
  (hextend : ∀ n φ m, P n (fun k => φ (k + m)) → P n φ) :
  ∃ φ, StrictMono φ ∧ ∀ n, P n φ
```

Construction (as the planner specified): nested extractors carried with their
strict-monotonicity proofs in a subtype `{φ // StrictMono φ}` (`Nat.rec`),
`G 0 = id`, `G (n+1) = G n ∘ ρ n` with `ρ n := (hstep n (G n) _).choose`; diagonal
`φ n := G (n+1) n`.  For each `n` the `n`-tail `fun m => φ (n+m)` equals
`G (n+1) ∘ τ` with `τ m := Q m (n+m)`, where `Q` is the partial composition of the
`ρ`'s past step `n+1` (`Q 0 = id`, `Q (m+1) = Q m ∘ ρ (n+1+m)`); `hGcomp :
G (n+1+m) = G (n+1) ∘ Q m` (induction).  `hsub` gives `P n` on the tail, `hextend`
lifts to all of `φ`.

Verified usable for the eventual C1b instantiation with `MapCInfConvOnCompacts`:
`hstep := exists_chart_cInfConv` (its `(B_r)` bound `∀k …` restricts to any
subsequence `∀k, … (φ k)`), `hsub := MapCInfConvOnCompacts.comp_subseq`, `hextend`
= the asymptotic `∃ k₀` shape of `MapCPConvOn`.

### Lean gotchas (C0)
- The recursion equations `G (n+1) = G n ∘ ρ n` and `Q (m+1) = Q m ∘ ρ (n+1+m)`
  are `rfl`; `rw` with them often auto-closes via its trailing `rfl` (drop the
  explicit `rfl`), EXCEPT the final comp-associativity `(f∘g)∘h = f∘(g∘h)` which
  is defeq but NOT syntactic after `rw` — needs an explicit trailing `rfl`.
- `StrictMono.le_apply : n ≤ f n` (implicit `n`) is the `ℕ→ℕ` ≥-id lemma;
  `strictMono_nat_of_lt_succ` builds `StrictMono` from `f n < f (n+1)`.
- `n + 1 + (j + 1)` is defeq `(n + 1 + j) + 1` (Nat succ), so the `Gf`-step at the
  shifted index closes by `show … ; rfl`-style without a `ring` rewrite.

## C1a / C1b — RESUMED 2026-06-12 (Brick C-G `smoothMetric_of_localCoeff` unblocks)

**Verified route (all seams confirmed before coding):**

1. **Frame identity (rfl).** The bridge's `hcoeff` is against
   `Geometry.frameVec x₀ i x = (trivAt x₀).symmL ℝ x (mdlBasis E i)` where
   `mdlBasis E := Module.finBasis ℝ E` (private, but DEFEQ to the public
   `Module.finBasis`).  `tangentConstInChart x₀ v p = (trivAt x₀).symmL 𝕜 p v`
   (NablaOnTensors.lean:474).  So
   `frameVec x₀ i = tangentConstInChart x₀ (Module.finBasis ℝ E i)` by `rfl`
   (privacy blocks the NAME `mdlBasis`, not definitional unfolding; write the RHS
   with the public `Module.finBasis ℝ E i`).  Hence the engine's section
   globalizer `exists_section_eqOn_compact x₀ (Module.finBasis ℝ E i)` produces a
   global `ContMDiffSection` equal to `frameVec x₀ i` near a compact.
2. **Engine output = frameVec component.** `exists_chart_cInfConv` converges
   `χ · writtenInExtChartAt x₀ (component)`; `writtenInExtChartAt_real_apply` gives
   value `= component ∘ (extChartAt).symm`, and `covDerivOfField gRef A0 0 = A0`,
   so at `y ∈ K₀` (χ=1) the converged scalar is `(gSeq k).inner y (V 0 y)(V 1 y)`.
   Feed `V = ![frameVec x₀ i globalized, frameVec x₀ j globalized]`.
3. **Typeclass.** The bridge needs `[InnerProductSpace ℝ E]` on the MODEL (for
   `posDef_isVonNBounded`); MetricPreconv's lemmas need only `[NormedSpace ℝ E]`.
   `InnerProductSpace` extends `NormedSpace`, so declaring `E` an inner-product
   space satisfies BOTH (matches Brick C-G's own assumption — consistent down the
   consumer chain).
4. **`hpos` from `hlow`.** C1b takes `hlow : ∃ c, 0 < c ∧ ∀ k x v,
   c * gRef.inner x v v ≤ (gSeq k).inner x v v` (eq 3.3 shape; cf.
   `metric_lower_bound_of_compact`).  Then `gm x v v = lim ≥ c·gRef x v v > 0`
   for `v ≠ 0` (gRef `.pos`).
5. **`gm` existence (pointwise CLM limit).** Diagonal (C0) over a countable
   (chart × n² component) cover (C1a, via `compactCovering` + finite chart
   subcovers) gives ONE `φ` with frameVec-components converging C∞ on every cover
   compact `Kₙ`.  At `y ∈ Kₙ` the n² components against the basis
   `{frameVec x₀ⁿ i y}` (basis since `y ∈ baseSet`) converge ⇒ finite-dim ⇒ the
   CLM `(gSeq(φk)).inner y` converges (`FiniteDimensional.complete`,
   `continuous_equivFun_basis`).  Define `gm y := limUnder atTop (...)`
   (`Tendsto.limUnder_eq`, `tendsto_nhds_limUnder`).  `Kₙ` cover `M` ⇒ defined
   everywhere.
6. **`hcoeff` ∀ x₀ (incl. non-cover charts) by engine re-run + limit uniqueness.**
   For arbitrary `x₀`, globalize `frameVec x₀ i,j` on a compact `K₀ ⊆ baseSet`,
   run `exists_chart_cInfConv` on `gSeq ∘ φ` → smooth `Φinf` + a further `ψ`.
   `gm`-component `= Φinf ∘ extChartAt` on `K₀` by uniqueness of pointwise limits
   (gm = lim along φ ⇒ same along φ∘ψ) ⇒ smooth on `K₀`; cover `baseSet` by such
   `K₀` ⇒ `ContMDiffOn baseSet`.
7. **Assemble** `smoothMetric_of_localCoeff gm hsymm hpos hcoeff` ⇒ `gInf` with
   `gInf.inner = gm`.  Endpoint: `∃ φ, StrictMono φ ∧ ∃ gInf, [component C∞ conv]`.

**Endpoint target** (C-II `metricCInfConvOnCompacts_of_normConv` consumes
`metricDerivNorm`, and the metricDerivNorm bridge C2 is itself scaffolded): C1b
delivers `∃ φ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M, [per-chart
frameVec-component `MapCInfConvOnCompacts` of gSeq(φk) → gInf]`.

## C1a / C1b — (historical) STOPPED note, planner decision required

### What was checked FIRST (per the prompt)

`SmoothRiemannianMetric I M = Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`
(`Geometry/Metric/Basic.lean`).  The Mathlib constructor
(`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:244`) has FIVE fields:
1. `inner (b : M) : T_b M →L[ℝ] T_b M →L[ℝ] ℝ` — the **intrinsic** fibrewise
   bilinear form (a CLM), NOT chart-component scalars;
2. `symm`, 3. `pos`, 4. `isVonNBounded (b) : IsVonNBounded ℝ {v | inner b v v < 1}`;
5. `contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L F →L ℝ)) ∞ (fun b => TotalSpace.mk'
   … (inner b))` — smoothness of the metric as a section of the **bilinear-forms
   bundle**.

### Why C1b is blocked (the foundational gap)

The Brick-B engine delivers limits as **chart-coordinate scalar functions**
`Φinf : E → ℝ` (one per chart × component), `ContDiff ⊤`.  Packaging them into
`gInf : SmoothRiemannianMetric` requires the **inverse of the entire `componentize`
layer**: reconstruct an intrinsic, globally smooth `(0,2)` field (fields 1 + 5)
from a chart-compatible family of `ContDiff` component functions, with overlap
consistency.  This bridge DOES NOT EXIST in the project:
- No constructor `Tensor0SField`/`SmoothRiemannianMetric` from real component
  functions (grep: only the forward `metricTensorField`).
- The project explicitly documents the general gate as unavailable:
  `Analysis/Spectral/.../DeTurck/NonlinearitySpectral.lean:53` —
  "`TensorL2 → SmoothRiemannianMetric` — *the gate, NOT available*".
- The ONLY metric-realization that exists,
  `TensorHsRealize.exists_smooth_metric_of_smooth_tensor_small`, builds `g + h`
  from a **`SmoothCcTensor`** (intrinsic, compactly-supported, `gFibreOpBound`
  fibre-small, `δ' < 1`).  It is inapplicable here twice over: (i) it consumes an
  intrinsic smooth section, not chart components — so it still needs the inverse-
  componentize bridge to even produce its input; (ii) it is a small/compactly-
  supported PERTURBATION of a fixed `g`, whereas `gInf` is a GLOBAL `C^∞` limit
  that need not be a `C⁰`-small perturbation of `gRef`.

Building the inverse-componentize / "smooth intrinsic metric from chart-compatible
component family" layer is a multi-lemma foundational addition (local-frame
coefficient smoothness `contMDiffOn_iff_localFrame_coeff` for the bilinear-forms
bundle + overlap gluing + `isVonNBounded`/`pos` from the lower bound).  The
planner's own Brick-B note flags Frontier 2 (σ-compact atlas, = C1a) and the
limit-object (C1b) as "one design unit," and the planner ruling reserved that
unit for Brick C-I.  Per the prompt's explicit instruction ("if the
SmoothRiemannianMetric packaging needs new foundational structure, STOP and
report — a planner decision, not yours"), C1a/C1b are NOT built in a vacuum.

### Building blocks located for the planner (when C1b is unblocked)
- Atlas (C1a): `compactCovering X : ℕ → Set X` + `isCompact_compactCovering`,
  `iUnion_compactCovering`, `exists_mem_compactCovering`
  (`Mathlib/Topology/Compactness/SigmaCompact.lean`); combine with per-compact
  finite chart subcovers (manifold local compactness) → countable
  (chart, inner-compact) family covering `M`.
- Per-item extractor (hstep for C0): `exists_chart_cInfConv` (MetricPreconv.lean).
- Diagonal: `exists_diag_subseq` (this file, DONE).
- Closest-but-insufficient realization gate:
  `TensorHsRealize.exists_smooth_metric_of_smooth_tensor_small`.

### Options for the planner
1. Build the inverse-componentize bridge ("smooth intrinsic `(0,2)` field /
   `SmoothRiemannianMetric` from a chart-compatible family of `ContDiff`
   components") as a dedicated foundational brick, then resume C1a/C1b.
2. Reformulate the P3 limit object to carry the limit as **chart-component data +
   intrinsic pointwise limit** (avoiding the smooth-metric packaging) if a
   downstream consumer can accept that — but `metricPreconvInf` / the P4
   `SourceDomainMetricData.limitMetric` both require a `SmoothRiemannianMetric`,
   so this likely needs a consumer-side change too.
3. Supply `gInf` as a hypothesis to the P3 endpoint (as Brick D's `windowPreconv`
   already does with its `gInf` argument), deferring the construction.

## 2026-07-09: order-dependent reference extraction

The earlier fixed-reference limitation is now removed for the smooth-limit spine. The checked
`exists_frame_refs`, `exists_allcomp_refs`, and `exists_limit_refs` route consumes bounds relative
to `gRef r` for all derivative orders `q <= r`. The checked endpoint `metricPreconv_refs` produces
a genuine `SmoothRiemannianMetric` using a separate fixed `gBase` only for the uniform positive
lower bound. The old fixed-reference declarations remain unchanged.

Focused verification passed. This closes the smooth-limit half of the D2 extraction problem; full
`MetricCInfConvOnCompacts` convergence is handled by the corresponding assembly wrapper rather than
by weakening this theorem's conclusion.
