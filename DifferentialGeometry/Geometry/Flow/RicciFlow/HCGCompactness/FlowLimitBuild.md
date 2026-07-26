# FlowLimitBuild.lean — P4 Brick 6, the L-term packaging (scoping + build note)

Plan: `P4_CONV_PLAN.md` Brick 6 (L-term/regularity/scalar wiring; the `equation`
bridge `metricLimit_pde` ∘ `ricciConv_of_dnConv` had already LANDED separately).

## Phase A — scoping findings (2026-07-02)

### What the L term actually is

- `SolutionFamily` (Core.lean:193) carries ONLY `metric : ℝ → SmoothRiemannianMetric I M`.
  `connection`/`ricciAt`/`rm04`/`scalar` are DERIVED accessors (Levi-Civita and canonical
  curvature of `metric t`). So the plan's "base curvature data (`rm04`/`ricciAt` fields
  of `SolutionFamily`) := canonical ones of gInf" is AUTOMATIC — there are no such fields
  in the current code. The whole S-term is `{ base := { metric := gInf } }`.
- `PointedFlowData` (HCGCompactness/Basic.lean:38) = 8 manifold/point fields
  (M, topology, charted, smooth, sigmaCompact, t2, t2TangentBundle, basepoint) + `S` +
  `isSolution`. `PointedRiemannianManifold` (PointedRiemannian.lean:36) has EXACTLY the
  same 8 fields + `metric` (it DOES carry `t2TangentBundle`, so the copy is lossless).
  Hence the constructor is a pure field copy from `P` plus `S := ⟨⟨gInf⟩⟩` + `hsol`,
  and `atTime t` of the result differs from `P` only in `metric := gInf t` — the
  reduction lemma is `cases P; subst (gInf t = P.metric); rfl`.

### Field-by-field demands of the 9-field `IsSolutionOn` (Core.lean:508)

| field | demand | source for the limit flow |
|---|---|---|
| `smoothMetric : MetricFamilySmoothOn D S.family` | 4 sub-fields (MetricFamily.lean:545): `coeff` = per-(x,X,Y) time-C^∞ on `D.regular`; `coeff_cont` = time-C⁰ on `D.carrier`; `metricTensor_cont` = JOINT (t,x) total-space C⁰ on `D.carrier`; `frameCompSmooth` = **JOINT (t,x) C^∞** of frame components on `D.regular ×ˢ u` for every C^∞ local frame | honest HYPOTHESIS (the known hard frontier: AA gives per-time C^∞ + time-Lipschitz only; see routes below) |
| `smoothConnection : ConnectionFamilySmoothOn` | PER-TIME spatial smoothness of LC connection (Connection/Smoothness.lean:48) | FREE: `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative` per time (needs only `[SigmaCompactSpace M] [T2Space M]`, noncompact-safe) |
| `equation : MetricVariationEquationOn` | `∀ t : RegularTime D, ∀ x X Y, HasDerivWithinAt (coeff) (−2·toTensorField ricciAt) D.carrier t` | hypothesis in `HasDerivAt`-at-regular-times/`ricciTensor` vocabulary (matches `metricLimit_pde(On)`: window `Icc` derivative + `Icc_mem_nhds` upgrades to `HasDerivAt` since `D.regular` is open); builder absorbs `metricRicciAt_apply_eq_ricciTensor` + `.hasDerivWithinAt` |
| `scalarCont` | joint C⁰ of `S.scalar` on `D.carrier ×ˢ univ` | honest HYPOTHESIS stated against `metricScalarAt (gInf t) x` (discharger: `chartScalar_jointContinuousOn`/`scalarCont_interior_of_chartGram`-style from the joint package) |
| `scalarTime` | `DifferentiableWithinAt ℝ (t ↦ scalar) K t` for `K ⊆ carrier` | HYPOTHESIS at the `D.carrier` level; `.mono` gives all K |
| `ricciCont` | `Tensor0SFamilyContinuousOnSet 2 D.carrier (S.ricci)` | honest HYPOTHESIS against `metricRicciAt (gInf t) x` (discharger: `ricci_continuous_in_metric_time` companions / `ricciCont_interior_of_chartGram`-style) |
| `rm04Cont` | same, valence 4, `S.base.rm04` | honest HYPOTHESIS against `metricRm04At (gInf t) x` |
| `ricciNormSpace` | per-time spatial `MDifferentiableAt` of `\|Ric\|²` | FREE: `normSq02_smooth` + congr (per-time, no time regularity) |
| `ricciNormGrad` | per-time smoothness of the `\|Ric\|²`-gradient field | FREE: `normSq02_smooth` + `gradientFun_mdiffAt` |

So of 9 fields: 3 are free (per-time facts about each smooth metric `gInf t`), 6 need
inputs, of which 1 (`equation`) is already produced by the landed bridge and 5 are
honest analytic statements about `gInf` (1 joint-C^∞ package + 4 curvature-continuity /
time-differentiability statements).

### Route ruling (plan's REGULARITY-ROUTE NOTE options)

**(2) `isSolutionOn_of_extendData` is NOT reusable, twice over:**
- its whole file (`Evolution/ExtendedSolutionRegularity.lean`) is under
  `[CompactSpace M]` — the HCG limit manifold M∞ is noncompact;
- it is `RealTimeInterval.closedOpen α b`-specific AND consumes a pre-existing solution
  `(S, hS)` on a left sub-interval `[α, ω)` for all four closed-endpoint boundary halves
  (scalarCont/scalarTime/ricciCont/rm04Cont glue interior `_of_chartGram` producers with
  `hS`-halves via `hagree`). The AA limit has no prior solution.
Its INTERIOR sub-builders (`metricFamilySmoothOn_of_chartGram`,
`ricciCont/rm04Cont/scalarCont/scalarTime_interior_of_chartGram`,
`metricVariationEquationOn_of_pde`) are also `Ioo/Ico`-hardcoded and CompactSpace-scoped;
generalizing them is real work and still would not give carrier-boundary continuity.

**(1) is the ruling: `MetricFamilySmoothOn` read carefully is NOT "per-time + frame
package" — `frameCompSmooth` genuinely demands joint interior (t,x)-C^∞, and `coeff`
demands per-point time-C^∞.** So the L-term builder CANNOT self-discharge it from AA
outputs; it stays the one hard input. Option (3) (PDE bootstrap: ∂ₜ-jets from spatial
jets via ∂ₜg = −2Ric) or the book's spacetime-AA (chapter3.tex:842–846) is the eventual
discharger — a separate brick. The builder therefore takes `MetricFamilySmoothOn` (the
canonical predicate, not an invented wrapper) as its regularity input.

**Decision: direct-fill builder** `isSolutionOn_of_reg` on a GENERAL `D : RealTimeInterval`
(the `FlowLimitData.L` field needs interval `X.D`, which is arbitrary — another reason
extendData's closedOpen shape is out), with the 3 free fields discharged internally and
the 5 honest inputs named. All ingredients verified noncompact-safe (LC-smooth,
`normSq02_smooth`, `gradientFun_mdiffAt` live under `[SigmaCompactSpace] [T2Space]`
only; `metricRicciAt_apply_eq_ricciTensor` additionally needs `[BoundarylessManifold I M]`
+ `[InnerProductSpace ℝ E]` + `[NeZero (finrank ℝ E)]` — available in the HCG context
via `[I.Boundaryless]`).

### `ScalarPullbackTendsto` finding (Brick E) — ⚠ quantifier alert

`ScalarPullbackTendsto Phi` (PointedConvergence.lean:1729) demands pointwise convergence
`scalar_k t (Phi.map k x) → scalar_∞ t x` for **ALL t : ℝ** (not just carrier times) and
all `x : L.M`. Off `D.carrier` the sequence flows are unconstrained data, so the ∀t
demand can only be discharged from per-t convergence hypotheses that Brick 5's window
machinery does NOT provide off-carrier. This is a pre-existing shape of the settled
`SmoothCGHConverges` API (not introduced here). Consequence: the Brick-6 scalar producer
must either (a) be fed a per-(t,x) hypothesis quantified over all t (honest, and exactly
what the trace lemma below produces pointwise), or (b) the endpoint definitions get
weakened to carrier times (public-API change — user decision). Flagged to the planner.

### The scalar trace step (analytic core) — precise remaining frontier

scalar = metric trace of Ricci.  The right endpoint is the exact mirror of the landed
Ricci pair (`ricciSub_le_dNorm` → `ricciConv_of_dnConv`), to be added in
`RicciFromJets.lean` (canonical home; its PRIVATE helpers are needed):

```
scalarSub_le_dNorm (gRef x) (lam B) (hlam : 0 < lam) (hB : 0 ≤ B) :
  ∃ C, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
    (lower bounds lam·gRef ≤ u, u' at x) → (cov bounds ≤ B, orders a ≤ 2, at x, both) →
    |metricScalarAt u x − metricScalarAt u' x|
      ≤ C * ∑ a ∈ Finset.range 3, metricDerivNorm a u u' gRef x
```

then `scalarConv_of_dnConv` (same hypothesis package as `ricciConv_of_dnConv`,
conclusion `∀ ε > 0, ∃ k0, ∀ k ≥ k0, ∀ t ∈ Icc β ψ, |metricScalarAt (gSeq k t) x −
metricScalarAt (gInf t) x| < ε`) is a VERBATIM copy of `ricciConv_of_dnConv`'s
ε-management.  Assembly recipe for `scalarSub_le_dNorm` (all ingredients checked to
exist, 2026-07-02):

1. Trace expansion at `α := x`: `metricScalar_chartTrace_eq`
   (RicciContinuityInMetricTime.lean:1292, `[I.Boundaryless]`) with
   `hx := chartLeviCivitaGoodSet_self` (exists — used in `ChartBridge/Hessian.lean`).
   NB the Ricci factor there is the INTRINSIC `ricciTensor` at `chartBasisVecFiber`
   slots (not `chartRicciTensor`), so `ricciSub_le_dNorm` applies directly per slot pair.
2. Split `Σ_{ij} invG_u·Ric_u − invG_{u'}·Ric_{u'}
   = Σ_{ij} (invG_u − invG_{u'})·Ric_u + Σ_{ij} invG_{u'}·(Ric_u − Ric_{u'})`.
3. `|Ric_u(e_i,e_j) − Ric_{u'}(e_i,e_j)| ≤ C·ΣdNorm`: `ricciSub_le_dNorm`
   (v := chartBasisVecFiber x i x, w := … j …).
4. `|invG_{u'}| ≤ Mb`: `invGram_le_of_low` (:1205).  Watch the value bridge
   `chartInvGramOnE g x i j (extChartAt I x x)` vs `chartInvGramMatrix g x x i j`
   (the trace lemma is stated in `OnE` form, the bound in `Matrix` form — find/add the
   one-line evaluation bridge).
5. `|invG_u − invG_{u'}| ≤ n²·Mb²·maxEntry|Gram_u − Gram_{u'}|` via
   `A⁻¹ − B⁻¹ = A⁻¹(B − A)B⁻¹` (3 lines from `Matrix.nonsing_inv_mul`/`mul_nonsing_inv`;
   dets are units by `chartGramMatrix_det_pos`), then order-0 entry difference ≤ dNorm
   via `gram0_le` (PRIVATE, RicciFromJets.lean:469 — same-file access).
6. Cross-term single-metric bound `|Ric_u(e_i,e_j)| ≤ MRic`: gRef-anchor —
   `ricciSub_le_dNorm` applied to the pair `(u, gRef)` with `lam' := min lam 1`,
   `B' := max B B0` where `B0 := max_{a≤2} metricCovDerivNorm a gRef gRef x` (a FIXED
   real at fixed x — constants may depend on (gRef, x)), plus the fixed real
   `|ricciTensor gRef x e_i e_j|`; `metricDerivNorm a u gRef gRef x ≤ covNorm(u) +
   covNorm(gRef)` by the banked `derivNorm_le_cov_add` (MetricPreconvWindowAllPt).

Estimated volume: one focused session (≈200–300 lines in the file's calc style).
After it: Brick E per-(t,x) = scalar diffeo/restriction invariance chain
(`metricScalarAt_restrictOpen` banked in Brick 1 + the pullback scalar eval banked in
SolutionPullback) + eventually-`x ∈ source k` + `scalarConv_of_dnConv` at `z = x`,
giving the tendsto at each (t, x) with t in a carrier window — the ∀t:ℝ quantifier of
`ScalarPullbackTendsto` (see the alert above) is then the only remaining gap and is a
planner/API decision, not analysis.

## Phase B — what landed (2026-07-02, VERIFIED)

`FlowLimitBuild.lean` — targeted build GREEN (`Build completed successfully, 3692
jobs`), all four endpoints `#print axioms = [propext, Classical.choice, Quot.sound]`
(no sorryAx; prints removed after reading):

- `isSolutionOn_of_reg` (namespace `DifferentialGeometry.PDE.RicciFlow`) — the 9-field
  `IsSolutionOn` builder for `{ base := { metric := g } }` on GENERAL `D`, from the
  honest inputs (`hsmooth : MetricFamilySmoothOn`, `hpde` in HasDerivAt/ricciTensor
  form, `hscalarCont`, `hscalarTime`, `hricciCont`, `hrm04Cont`); the three per-time
  fields discharged internally.  Section carries
  `[InnerProductSpace ℝ E] [NeZero (finrank ℝ E)] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I (∞+1) M]` (demanded by the Reconcile bridge and
  `SolutionOn`'s signature; all derivable at HCG call sites).
- `flowOfMetric` (namespace `DifferentialGeometry.HCGCompactness`) — the
  `PointedFlowData D` constructor from `(P : PointedRiemannianManifold) (g) (hsol)`,
  pure field copy (defeq-preserving, KEY-fact-5 compatible: `(flowOfMetric …).M` is
  definitionally `P.M`).
- `flowOfMetric_metric` — `(flowOfMetric …).S.base.metric = g` (rfl; Brick 5's
  hard-wiring hook; `SolutionOn.family_metric` bridges to `.family.metric`).
- `flowOfMetric_atTime` — `g t = P.metric → (flowOfMetric D P g hsol).atTime t = P`
  (the Brick-7 `hL0` producer, stated at any time `t`).

Intended dischargers of the builder hypotheses (Brick 5/7 + the regularity brick):
- `hsmooth` — the ONE remaining hard frontier (joint regularity; route (3) bootstrap or
  spacetime AA; separate brick).
- `hpde` — `metricLimit_pdeOn` on a neighborhood window + `HasDerivWithinAt.hasDerivAt`
  via `Icc_mem_nhds` (D.regular open ⊆ carrier via `regular_mem_nhds`).
- `hscalarCont`/`hricciCont`/`hrm04Cont`/`hscalarTime` — from the joint package /
  `ricci_continuous_in_metric_time` companions (RicciContinuityInMetricTime.lean:1154,
  1292, 1338) once `hsmooth`'s discharger exists; these are strictly-weaker consequences
  of the same joint regularity.

## Verification

Focused check passed; targeted `build +…FlowLimitBuild` GREEN (3692 jobs); all four
endpoints axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`);
temporary `#print axioms` removed and the file re-checked green.  (The one
`declaration uses 'sorry'` warning in the build log is the pre-existing, unrelated
`Tensor/RSTensor/Coordinates/Field.lean:282`.)

## Gotchas (for the next session)

- ASCII `forall` does NOT support the `∈`-binder sugar (`forall t ∈ s` is a parse
  error); use `∀ t ∈ s`.
- Statement-level dot-projections through an OPAQUE application
  (`(flowOfMetric …).S.base.metric`) trigger instance SYNTHESIS on
  `(flowOfMetric …).M`, which reducible-transparency search cannot see through (the
  def is not `@[reducible]`).  Fix: prelude the conclusion with `letI` keyed on the
  application's own projections (`letI : TopologicalSpace (flowOfMetric …).M :=
  (flowOfMetric …).topology`, …) — the `ScalarPullbackTendsto`/`FlowLimitData` idiom.
  A `letI` keyed on `P.M` does NOT help (search won't unfold `flowOfMetric` to see
  `(flowOfMetric …).M ≡ P.M`).
- Structure-literal fields whose type needs instances (the `S :=` field of the
  constructor): wrap the VALUE in its own `letI` chain + type ascription (mirroring
  `Basic.lean`'s `atTime`, which uses a tactic block for the same reason).
- `cases P` + `subst h` on a structure with instance-implicit fields FAILS here
  ("failed to create binder when reverting variable dependencies"): after `cases P`,
  the letI-typed parameters `g`/`hsol` mention `(mk …).topology` — i.e. the
  destructured fields — and subst cannot re-abstract.  Robust replacement: NO
  destructuring — `exact congrArg (fun m => ({ …fields from P…, metric := m } :
  PointedRiemannianManifold (I := I))) h`, which typechecks by structure ETA
  (`{…, metric := P.metric} ≡ P`) plus the definitional unfolding of `atTime`.
- `flowOfMetric_metric` is intentionally NOT `@[simp]` (letI-wrapped statements make
  poor simp lemmas); at Brick 7 the identification holds by `rfl` against the concrete
  term anyway.
