# RicciFromJets.lean — P4 Brick 6 `hRicConv` producer (plan, 2026-07-02)

Target: discharge the "missing conversion lemma" of `LimitSolutionEquation.md` —
uniform Ricci convergence from C²-covariant metric convergence.  Consumer shape
(`LimitSolutionEquation.lean:225`, `hRicConv`):
`∀ ε > 0, ∃ k0, ∀ k ≥ k0, ∀ u ∈ Icc β ψ, |ricciTensor (gk u) x v w − ricciTensor (gInf u) x v w| < ε`.

## Route decision (surveyed 2026-07-02)

Route (b) (covariant ∇ᵍ−∇ʰ difference calculus) confirmed absent (no curvature-of-
modified-connection formula anywhere; Lemma45/C4 layer is component-world derivative
comparison, not curvature differences).  Route (a) (chart) chosen, in **modulus form**
(a per-pair quantitative estimate needs no time-continuity of `gInf` and no per-k
joint smoothness — both of which the continuity-chain route would require).

**Key discovery 1 (kills diagnosis gap 1):** the covariant→chart-jet conversion
identity already exists as the P3 tower engine:
- `fderiv_chartRep_eq_towerStep` (`MetricPreconv.lean:537`) — germ identity
  `∂_v (chartRep s_p^V) =ᶠ[𝓝 α] chartRep (towerStep gRef A0 p V σ)`;
- `towerStep` (`MetricPreconv.lean:516`) = level-(p+1) scalar + Christoffel-free
  corrections (slots updated by `∇̂_σ V_a`), **metric-independent slots**;
- `bumpTowerStep_split` (`ComponentConvTower.lean:320`, take χ ≡ 1) re-expresses
  `chartRep (towerStep)` as a sum of chartReps of tower scalars with `covSection`
  slots (bundled smooth sections — `NablaOnTensors/Connection/Tangent.lean:50`).
Iterating twice: the ≤2 chart jets of `chartGramOnE` at α = `extChartAt I x x` are
finite sums of `covDerivOfField gRef A0 p x (explicit slot vectors)`, p ≤ 2.
CS-eval `abs_apply_le_sqrt_normSq0S` (`Tensor0SRiemannian/Comparison.lean:711`,
gRef-ON basis from `exists_gOrthonormalBasis`, `RicciOperatorNormBound.lean:38`)
bounds each term by `metricDerivNorm`/`metricCovDerivNorm` × fixed slot-norm
constants.  `metricCovDeriv_eq_covDerivOfField` is `rfl`
(`MetricCovDerivLinear.lean:89`).

**Key discovery 2 (kills diagnosis gap 2):** the "private continuity-only chartRicci
algebra" has a PUBLIC QUANTITATIVE twin — the DeTurck-coefficient Lipschitz layer
(`Analysis/Spectral/Intrinsic/DeTurckCoefficients/`):
- `InverseGramPerturbation.lean`: `chartInvGramMatrix_entry_sub_abs_le_gramDiffSup`
  (pair-uniform-ready: takes explicit `M_b` bounds), `chartGramDiffSup`.
- `ChristoffelPerturbation.lean`: `chartMetricJet2DiffSup` (the pointwise 2-jet
  difference aggregate at (α,y) — exactly my Part-1 output), `chartChristoffel_sub_abs_le`
  (:384), `partialDeriv_chartChristoffel_eq` (:600, public ∂Γ Leibniz),
  `partialDeriv_chartInvGramOnE_sub_abs_le` (:662), `partialDeriv_chartChristoffel_sub_abs_le` (:865).
- `RicciDiffAffine.lean`: split `chartRicciTensor_eq_secondOrder_add_firstOrder`,
  `chartRicciSecondOrderTerm_sub_abs_le` (:433), `chartRicciFirstOrderTerm_sub_abs_le`
  (:479), and the per-pair endpoint `exists_chartRicciTensor_lipschitz_on_compact`
  (:631) whose constant is per-pair only because the `exists_*_on_compact` wrappers
  bake in per-metric continuity bounds; the pointwise lemmas underneath take all
  bounds as hypotheses ⇒ mirror the :631 assembly with **pair-uniform** inputs.
- `partialDeriv_chartInvGramOnE_eq` (`HessianTrace.lean:1325`) for the D-bound
  (|∂G⁻¹| from M_b, Q).

Bridge (both metrics, metric-independent coefficients):
`ricciTensor_eq_chartRicciSwap_of_basis_identity` (`ChartBridge/Ricci.lean:301`) +
`chartRiemannBasisIdentity_holds` (`ChartBridge/RiemannBasisIdentity.lean:543`,
unconditional).

## File plan (`RicciFromJets.lean`, this folder)

1. **Jet expansion (Part 1, the diagnosed crux).**
   - `partialDeriv m (chartRep s_p^W)(α) = (covDerivOfField A0 (p+1)) x (cons) + Σ_a
     (covDerivOfField A0 p) x (update-covSection)` — generic p, from the germ identity
     with Kc = {x} (`exists_section_eqOn_compact` for σ's with v = chartModelBasis E m).
   - Germ bridge `chartGramOnE u x i j =ᶠ[𝓝 α] chartRep (s_0(metricTensorField u))`
     (via `tangentConstInChart`/`chartBasisVecFiber` = `symmL`/`symm`).
   - Order-2 by re-application on the towerStep pieces (differentiability from
     `chartRep_towerScalar_contDiffOn`).
   - CS packaging: `∃ C > 0` (depends on x, gRef only): `chartMetricJet2DiffSup u u' x α
     ≤ C·Σ_{a≤2} metricDerivNorm a u u' gRef x`; single-metric jet bounds
     `≤ C·Σ_{a≤2} metricCovDerivNorm a u gRef x`.
2. **Inverse-Gram entry bound from metric lower bound at x** (elementary, no
   spectral API): `lam·gRef ≤ u` at x + gRef-ON-basis change-of-coordinates (entrywise
   CS, constant `c₀ = 1/(1+ΣQ²)`) ⇒ `ξᵀGξ ≥ lam·c₀·Σξ²`; inverse column trick
   (`μN² ≤ ηᵀGη = η_q ≤ N`) ⇒ `|G⁻¹ entries| ≤ 1/(lam·c₀)`.  Uses
   `chartGramMatrix_posDef`/`_mul_chartInvGramMatrix` (`ChartGram.lean:299`,
   `Gradient.lean:195`).
3. **Pair-uniform chartRicci difference** — mirror `exists_chartRicciTensor_lipschitz_on_compact`
   with constants from (1)+(2) instead of per-pair compact-continuity bounds.
4. **Endpoints.**
   - `ricciTensor_sub_le`: ∃ C (from x, gRef, lam, B, v, w), ∀ u u' with lower bound
     lam and covariant bounds B (orders ≤ 2) at x:
     `|ricciTensor u x v w − ricciTensor u' x v w| ≤ C·Σ_{a≤2} metricDerivNorm a u u' gRef x`.
   - `ricciConv_of_dnConv` (the hRicConv producer): sequence/window form matching
     `metricLimit_pde`'s `hRicConv` verbatim, hypotheses = pointwise-at-x seminorm
     smallness (Brick 5's hconv at z = x) + window equivalence lower bounds + window
     covariant bounds for both `gSeq` and `gInf`.

## Status: DONE (2026-07-02, verified)

- [x] Route verified feasible end-to-end with named existing lemmas (this plan).
- [x] Part 1 (jet expansion + CS packaging): `sRep_pd_val`/`sRep_pd2_val` (tower
  identity iterated at Kc = {x}), `gram_germ` (chartGramOnE ↔ tower scalar germ),
  `gram0_le`/`gram1_le`/`gram2_le`, public `jet2Diff_le_dNorm` (THE conversion
  lemma) + `gramJet_le_covNorm` (single-metric jet bounds).
- [x] Part 2 (`invGram_le_of_low`): sphere-minimum `gram_quad_low` for the fixed
  gRef Gram form (no spectral API; `IsCompact.of_isClosed_subset` on
  `{ξ | ξ⬝ᵥξ = 1}` + `chartGramMatrix_dotProduct_mulVec` + `gRef.pos`), then the
  inverse-column trick (`μN² ≤ ηₗ ≤ N`).
- [x] Part 3 (`chartRicci_sub_le`): pair-uniform re-assembly of the DeTurck
  pointwise lemmas (constants Q, P, R, D, Mb, Cinv, Cd, Clip, Cdiff, Mg from
  Parts 1–2, mirroring `exists_chartRicciTensor_lipschitz_on_compact`).
- [x] Part 4 endpoints: `ricciSub_le_dNorm` (per-pair ∃C estimate, bridge via
  `ricciTensor_eq_chartRicciSwap_of_basis_identity` + unconditional
  `chartRiemannBasisIdentity_holds`; NB needed the extra import
  `ChartBridge.RiemannBasisIdentity` — `ChartBridge.Ricci` does NOT export it),
  `ricciConv_of_dnConv` (the hRicConv producer, window/sequence form, hypothesis
  shapes exactly consumable by Brick 5: pointwise-at-x hconv instance + window
  lower-equivalence + window covariant bounds for both families).
- [x] Verification: focused checks green throughout; targeted build
  `+…HCGCompactness.RicciFromJets` GREEN (3925 jobs, module freshly compiled);
  `#print axioms` on `jet2Diff_le_dNorm` / `ricciSub_le_dNorm` /
  `ricciConv_of_dnConv` = `[propext, Classical.choice, Quot.sound]` (no sorryAx;
  temporary prints removed, clean rebuild green, no warnings in this file).

## Scalar endpoints (P4 Brick 6 scalar bullet, 2026-07-03 pass)

Added `section ScalarEndpoints` (end of file): the scalar mirror of the Ricci pair,
per the recipe in `FlowLimitBuild.md` §"The scalar trace step".

- `scalarSub_le_dNorm` — per-pair estimate `|R(u) − R(u')| ≤ C·Σ_{a≤2} dNorm a u u'`
  with `C = C(gRef, x, lam, B)`; same hypothesis package as `ricciSub_le_dNorm`.
  Route: trace expansion `PDE.RicciFlow.metricScalar_chartTrace_eq` at `α := x`
  (`hx := self_mem_chartLeviCivitaGoodSet`, namespace `Integral.Connection`);
  split `Σ invG·Ric` difference into `(invG_u−invG_{u'})·Ric_u + invG_{u'}·(Ric_u−Ric_{u'})`;
  per-slot `ricciSub_le_dNorm` at `chartBasisVecFiber x i x` slots; `invGram_le_of_low`
  for `|invG_{u'}|`; new private `invGram_sub_le` (matrix identity `Matrix.inv_sub_inv`
  — Mathlib HAS `A⁻¹−B⁻¹ = A⁻¹(B−A)B⁻¹`, hypothesis `IsUnit A ↔ IsUnit B` discharged
  via `Matrix.isUnit_iff_isUnit_det` + `chartGramMatrix_det_pos`; entries via `gram0_le`);
  new private `ricci_abs_le` (gRef-anchor: `ricciSub_le_dNorm` on the pair `(u, gRef)`
  with `lam' := min lam 1`, `B' := max B B0`, `B0 := max of the three
  `metricCovDerivNorm a gRef gRef x`, pair seminorm via `derivNorm_le_cov_add`).
- `scalarConv_of_dnConv` — sequence/window corollary, ε-management copied verbatim
  from `ricciConv_of_dnConv`; conclusion `|metricScalarAt (gSeq k t) x −
  metricScalarAt (gInf t) x| < ε` uniformly on `Icc β ψ`.
- **The flagged OnE↔Matrix value bridge (recipe step 4) RESOLVED**: it already exists
  as `chartInvGramOnE_extChartAt_self`
  (`Analysis/Parabolic/RicciLinearization/RicciSymbolFormula.lean:78`), but importing
  that pulls the parabolic-linearization branch; since it is one `rw
  [chartInvGramOnE_def, extChartAt_to_inv]` (Mathlib `extChartAt_to_inv`), it is
  re-derived as an inline `have hbr` inside `scalarSub_le_dNorm` — no new import,
  no new public name.
- New imports: `ShortTimeAssembly.RicciContinuityInMetricTime` (trace lemma) and
  `HCGCompactness.MetricPreconvWindowAllPt` (`derivNorm_le_cov_add`); no cycles
  (nothing imported RicciFromJets).
- **Upstream fix (sanctioned by weakest-assumptions rule):**
  `metricScalar_chartTrace_eq` carried a GRATUITOUS `[CompactSpace M]` from its file's
  variable block (section-variable pollution — fatal for the noncompact HCG setting).
  Added `omit [CompactSpace M] in` at that one lemma
  (`RicciContinuityInMetricTime.lean`); its module rebuilt GREEN (9228 jobs), proving
  the hypothesis was never used.  Instance-hypothesis removal cannot break call sites.
- Verification status: upstream `RicciContinuityInMetricTime` targeted build GREEN;
  `PointedConvergence` (see below) rebuilt GREEN inside the RicciFromJets build
  attempt.  The RicciFromJets targeted build itself is BLOCKED by a parallel
  session's in-flight broken `ProductMFoldNorm.lean` (git-modified + lake-claimed by
  the ConvFieldAssembly agent; type errors at :373/:410; its `.olean` is currently
  absent, so even focused checks of anything through
  `MetricPreconv → RicBound → MetricCovDerivArityBridge` cannot load).  The scalar
  section has therefore NOT yet been compiled; axiom check pending.  Rerun
  `build +…HCGCompactness.RicciFromJets` once `ProductMFoldNorm` is green again.

## API change executed with this brick (PointedConvergence.lean)

`FunctionPullbackTendsto` / (hence) `ScalarPullbackTendsto` weakened from `∀ t : ℝ`
to `∀ t ∈ X.D.carrier` (planner ruling in P4_CONV_PLAN: off-carrier the flows are
unconstrained junk — the old statement was UNPROVABLE; the book, MSM135 Thm lbl335,
concludes convergence only on `(α, ω)`).  Consumer audit (project-wide grep, all
uses): `SmoothCGHConverges.scalar_converges` field + `ofSpacetime`/
`ofRestrictPullback` passthroughs + `FlowLimitData.scalar` field only STORE the Prop
— no change needed; `FunctionPullbackTendsto.le_of_bound0` (same file, consumed
nowhere) had its conclusion weakened to carrier times to match;
`HamiltonPositiveRicciAdapter.baseScalarConv_of_smoothCGH` applies it at `t = 0` and
gained an honest `(h0 : (0:ℝ) ∈ X.D.carrier)` hypothesis, discharged at its sole
call site (`toHam3Exists`) from `hwindow : Icc (−r0²) 0 ⊆ X.D.carrier` via
`neg_nonpos.mpr (sq_nonneg _)`.  No consumer used the `∀t:ℝ` strength.
`PointedConvergence.lean` rebuilt GREEN (job 969 of the blocked build).

## Lean gotchas (this pass)

- `ContDiffOn.differentiableOn` in current Mathlib takes `(hn : n ≠ 0)`, not
  `1 ≤ n` — `(by simp)` discharges `(∞ : WithTop ℕ∞) ≠ 0`.
- `Filter.EventuallyEq.fderiv'` does not exist; germ-of-fderiv is
  `hg.eventuallyEq_nhds` + `filter_upwards` + per-point `EventuallyEq.fderiv_eq`.
- `HasFDerivAt.sum` produces the Pi-sum `(∑ i, f i)` form; `simpa
  [Finset.sum_apply]` converts to `fun z => ∑ i, f i z`.
- dotProduct lemmas are unprefixed in current Mathlib (`smul_dotProduct`,
  `dotProduct_smul`), while `Matrix.mulVec_smul`/`mulVec_mulVec`/`one_mulVec`
  keep the `Matrix.` prefix.
- `SmoothMetric_gen` and `SmoothRiemannianMetric` are the SAME abbreviation
  (`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`) — pass a
  `SmoothRiemannianMetric` directly to `abs_apply_le_sqrt_normSq0S`.
- The numeral shapes `0+1+2` vs `3 = 1+2` etc. from `towVal_le` at literal `p`
  unify with `metricDerivNorm 1/2` by `rfl` (closed-Nat defeq) — state the
  identification `have hd : √(normSq0S … (covDerivOfField …)) = metricDerivNorm …
  := rfl` and `rw` it.
- One-step `calc a * (… + …) ≤ b := by …` with the relation on a continuation
  line mis-parses here; use `mul_le_mul` directly.
- The DeTurck chart lemmas need the parent files' heartbeat options
  (`maxHeartbeats 1600000`, `synthInstance.maxHeartbeats 800000`) at the
  consumer too.
- Multi-agent load: `failed to create thread` / `std::bad_alloc` on focused
  checks are TRANSIENT (parallel agents); the targeted `build` (serialized on
  the lake lock) went through.

## Findings so far (route survey)

- The two "genuine gaps" of `LimitSolutionEquation.md` are both already ~90% built,
  in trees the diagnosis pass did not search: the conversion identity lives in the
  P3 tower engine (`towerStep`, not indexed under "chart jets"), and the
  quantitative chart-Ricci algebra lives in `Analysis/Spectral/.../DeTurckCoefficients`
  (the diagnosis only found the `ShortTimeAssembly` continuity chain).
- For two-metric difference estimates, grep `DeTurckCoefficients`
  (`*Perturbation*`, `*DiffAffine*`, `*Lipschitz*`) first.
- Pair-uniformity discipline: constants FIRST (`∃ C, ∀ u u'`); the DeTurck
  `exists_*_on_compact` wrappers are NOT reusable (per-pair C), only their
  pointwise underlying lemmas are.

## Post-merge compatibility (2026-07-14)

- The `towerStep` difference proof stopped closing with `ring` after the
  short-time-existence alignment.  The mathematical identity is unchanged:
  evaluate each concrete `Tensor0SSpace` difference first, distribute the
  finite sum, and close in the additive group with `abel`.
- The generic `ContinuousMultilinearMap.sub_apply` simp argument in the
  chart-Gram base case was stale and has been removed.
- Focused verification passes without local warnings.  This is an upstream
  compatibility repair only; it does not change the already-complete
  `RicciFromJets` theorem surface.
