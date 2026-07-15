# Reconcile.lean — notes

Date: 2026-06-13. Verification: focused `lake env lean` PASSED (exit 0), no `sorry`.

## What this file provides

`leviCivitaConnectionOfMetric_apply_eq_leviCivita` — the previously-missing bridge between the
project's TWO Levi-Civita constructions:

- `LeviCivita g` (stitched, `Defs.lean:249`) — drives `ricciTensor`/`ricciEndo` + chart bridges.
- `leviCivitaConnectionOfMetric g` (= `metricCov`, Koszul, `KoszulFormula.lean:1021`) — drives
  `metricRicciAt`/`metricRm04` → `S.ricci`/`S.base.rm04`.

Statement: for differentiable `σ`, `(leviCivitaConnectionOfMetric g).toFun σ x v =
(LeviCivita g).toFun σ x v`.  Proof: `LeviCivita_unique` (Koszul uniqueness) fed
`leviCivitaConnectionOfMetric`'s torsion-free + metric-compatibility.

## The typeclass lesson (cost: ~8 failed configs before this)

The two LC worlds have a SHARED but easy-to-miss instance convention.  `Defs.lean:77-78`
declares BOTH `[NormedSpace ℝ E]` AND `[InnerProductSpace ℝ E]` (on a continuation line).
The correct block here mirrors it:
```
variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
```
- Declaring ONLY `NormedSpace`: the `leviCivitaConnectionOfMetric_isLeviCivita`/`_isMetricCompatible`
  facts fail (they/`IsLeviCivita` ultimately need the InnerProductSpace via shared machinery), and
  `NeZero` is needed.
- Declaring ONLY `InnerProductSpace`: the stitched-`LeviCivita` tangent-bundle `MDiffAt (T% σ)`
  `ChartedSpace` synthesis FAILS (`ChartedSpace (ModelProd H (ModelProd H E)) (TangentBundle)`,
  spurious double-`ModelProd`) — that infra is registered against the EXPLICIT `NormedSpace`.
- Declaring BOTH (the codebase convention) makes everything resolve.  Short-time analysis genuinely
  needs the inner product (per user), so this is the right setup, not weakening to NormedSpace.

Also: `[NeZero (Module.finrank ℝ E)]` is required by the lcOfMetric facts; and
`leviCivitaConnectionOfMetric_isMetricCompatible` returns the Connection-layer `IsMetricCompatible_gen`
(section-valued direction) whereas `LeviCivita_unique` wants the LeviCivita-layer `IsMetricCompatible`
(arbitrary direction `v`) — bridged inline via `metric_compatible_at_apply` + a smooth section through
`v` (`ContMDiffSection.exists_eq_at`).  `IsTorsionFree → torsion = 0` is `funext` (since
`IsTorsionFreeAt cov x := cov.torsion x = 0`).

## Next (toward `ricciCont`) — precise curvature-lift chain

The connection agreement (this file) is the foundation.  Remaining chain to `metricRicciAt = ricciTensor`
(every piece located, all curvature-algebra, no analytic/typeclass wall):

1. **cov-congruence of `connectionRiemannCurvatureField`** (`Curvature/Basic.lean:56`):
   `connectionRiemannCurvatureField (lcOfMetric g) X Y Z x = connectionRiemannCurvatureField (LeviCivita g) X Y Z x`
   for smooth `X Y Z`.  The field is `∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` with `∇_Y Z = fun y => (cov Z y)(Y y)`.
   - Term `(cov Z x)(lie X Y x)`: direct from the reconciliation (`Z` diff). 
   - Terms `(cov (∇_Y Z) x)(X x)`: first `∇¹_Y Z = ∇²_Y Z` pointwise (reconciliation on diff `Z`), giving a
     common section `S`; then `(lcOfMetric S x)(X x) = (LeviCivita S x)(X x)` by reconciliation — NEEDS
     `MDiffAt S x`.  **Sublemma: `S = ∇_Y Z` is smooth**, from `LeviCivita_section_contMDiffOn_univ`
     (`Defs.lean:306`, the Hom-bundle section `LeviCivita σ` is smooth) + `ContMDiff.clm_bundle_apply`
     applied to smooth `Y`.  (This is the only technical sub-step.)
2. **`riemannCurvatureAt` agreement**: via `riemannCurvatureAt_apply_smooth` (`Riemann/Basic/Sections.lean:176`,
   `riemannCurvatureAt cov x α (vec3 …) = cotangentToDual α (connectionRiemannCurvatureField cov X Y Z x)`),
   step 1 gives `riemannCurvatureAt (lcOfMetric g) = riemannCurvatureAt (LeviCivita g)` on smooth inputs,
   hence `metricRm13At g = riemannCurvatureAt (LeviCivita g)` (since `metricRm13At = riemannCurvatureAt (metricCov g)`,
   `metricCov = lcOfMetric`).
3. **`ricciFromRm13At` ↔ trace bridge** (within LeviCivita g): `metricRicciAt g = ricciFromRm13At (metricRm13At g)`
   (`Riemann/Basic/Pointwise.lean:657`, rfl) and `ricciTensor g = trace (ricciEndo)` (`RicciConnection.lean:232`).
   Reconcile via `ricciFromRm13At_apply_basis_trace` (`Components/Basic.lean:190`) + `ricciTensor_apply_basisSum`
   (`RicciConnection.lean:239`): both are the `chartModelBasis` trace-sum of the same `riemannOp (LeviCivita g)`.
   ⟹ `metricRicciAt g x (vec2 v w) = ricciTensor g x v w`.
4. **`ricciCont` consumer**: `tensor0SFamilyContinuousOnSet_of_chartBasisComp (N := goodSet)` on
   `S.ricci` (= `metricRicciAt (g t)`), rewrite the chart-frame component via (3), then
   `ricciChartFrameComp_jointContinuousOn` (`RicciContinuityInMetricTime.lean`).  `rm04Cont` is the
   `(0,4)` analog.

Checkpoint rationale: the LC connection reconciliation (this file) was the genuine roadblock; steps 1–4
are scoped curvature-algebra with all lemmas located.

### File placement + tooling for steps 1–4 (2026-06-13)

- **Cycle constraint:** steps 1–4 use `connectionRiemannCurvatureField`/`covApply`/`ricciTensor`
  (Curvature layer, DOWNSTREAM of `Connection/LeviCivita`).  They CANNOT live in `Reconcile.lean`
  (would cycle).  Create a new Curvature-layer file (e.g. `Geometry/Curvature/MetricLeviCivitaReconcile.lean`)
  importing `Connection.LeviCivita.Reconcile` + `Curvature.Basic` + `Curvature.CurvatureOperator.{Defs,RicciConnection,CurvatureBundling}` + `Curvature.Riemann.Basic.Sections` + `Curvature.Metric`.
- **Instance block:** both `[NormedSpace ℝ E] [InnerProductSpace ℝ E]` + `[FiniteDimensional]` `[CompleteSpace]`
  `[NeZero (finrank)]`, `[IsManifold I ∞ M]` AND `[IsManifold I ((∞:WithTop ℕ∞)+1) M]` (the `(∞+1)` is
  needed both for `(∞+1)`-`ContMDiffSection`s and `covApply_mdifferentiableAt_local`), `[SigmaCompact]`
  `[T2]` `[BoundarylessManifold I M]`.
- **Step-1 proof shape (cov-congruence):** `connectionRiemannCurvatureField cov X Y Z x` is defeq to
  `riemannSec cov X Y Z x = cov.toFun (covApply cov Y Z) x (X x) − cov.toFun (covApply cov X Z) x (Y x)
  − cov.toFun Z x (lie X Y x)` (`CurvatureOperator/Defs.lean:87`; `covApply cov X Z = fun b => cov.toFun Z b (X b)`).
  Take `X Y Z : ContMDiffSection I E (∞+1)`.  Proof:
  1. `covApply (lcOfMetric g) Y Z = covApply (LeviCivita g) Y Z` (funext + `covApply_apply` + the
     reconciliation on diff `Z`); same for the `X` slot.
  2. `MDiffAt (covApply (LeviCivita g) Y Z) x` via `covApply_mdifferentiableAt_local`
     (`CurvatureBundling.lean:81`; `hcov` = `LeviCivita_isContMDiff` instance, `hX = Y.mdifferentiableAt`,
     `hZ = Z.contMDiff` at `(∞+1)`); same for `X`.
  3. `show riemannSec … = riemannSec …; unfold riemannSec; rw [covApply-agreements]`, then rewrite the
     three `cov₁.toFun … = cov₂.toFun …` via the reconciliation (`recon hSY (X x)`, `recon hSX (Y x)`,
     `recon hZmd (lie X Y x)`), closing by rfl.  (Watch the `⇑cov` vs `cov.toFun` coercion in `rw`.)
  Steps 2–4 then proceed as above.  This is a substantial but fully-tooled multi-step proof — a focused
  follow-up session, not a quick brick.

### 2026-06-13 STEP 1 DONE (verified, exit 0, no sorry)

`Geometry/Curvature/MetricLeviCivitaReconcile.lean` (NEW, downstream of Reconcile + Curvature):
`connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita` — the curvature-field cov-congruence,
exactly as planned (covApply-agreement via the reconciliation on diff `Z`; `covApply_mdifferentiableAt_local`
for `MDiffAt (∇_Y Z)`; `show riemannSec …` defeq + `rw` the three terms via the reconciliation).
Used `(∞+1)`-`ContMDiffSection`s.  One fix: `SmoothRiemannianMetric` (not `Measure.SmoothRiemannianMetric`)
in the Curvature-layer namespace.  Note `ricciCurvatureAt_eq_trace` (`Pointwise.lean:654`) is just the
DEF `ricciCurvatureAt = ricciFromRm13At ∘ riemannCurvatureAt` (misleading name), NOT a trace bridge.

### 2026-06-13 STEPS 2–4 DONE (GREEN, one isolated frontier) — see `MetricLeviCivitaReconcile.md`

Steps 2, 3, 4 are all proved in `Geometry/Curvature/MetricLeviCivitaReconcile.lean`.  The public
bridge **`metricRicciAt_apply_eq_ricciTensor`** (`metricRicciAt g x (vec2 v w) = ricciTensor g x v w`)
now exists.  Steps 1+2 are sorry-free; steps 3+4 are proved modulo ONE isolated, fill-ready frontier
`riemannCurvatureAux_tangentConst_eq_riemannOp` (curvature tensoriality const↔smooth), blocked only by
two `private` locality lemmas in `Riemann/Basic/Sections.lean` (lines 22, 67).  Smallest unblock =
de-privatize those two, then a 3-line fill.  Full details + gotchas in `MetricLeviCivitaReconcile.md`.

Next: `ricciCont`/`rm04Cont` consumer wiring (`tensor0SFamilyContinuousOnSet_of_chartBasisComp` on
`S.ricci` + this bridge + `ricciChartFrameComp_jointContinuousOn`).
