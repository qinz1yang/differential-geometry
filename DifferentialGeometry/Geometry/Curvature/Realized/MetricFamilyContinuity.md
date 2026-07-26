# MetricFamilyContinuity.lean — notes

## 2026-07-12: short-time branch alignment compatibility

`Tensor0SFamilyContinuousOnSet.pullback` failed after the branch alignment because its terminal
`simp only` no longer matched the displayed composition application. The needed
`ContinuousMultilinearMap.compContinuousLinearMap_apply` equality is definitional in the current
API, so the terminal proof is now `rfl`. Focused verification and the targeted module build both
passed. The theorem and its dedicated pullback-continuity machinery are complete (100%); this was
a local API compatibility repair, not new Hamilton or HCG theorem progress.

The same alignment had removed the public
`metricCLMSection_jointContMDiffOn_of_chartGram` producer from the conjugating-flow assembly file
while the local evolution consumer still uses it. Its chart-coordinate helper and theorem were
moved here, their natural metric-family continuity layer, under only the local
`NeZero (Module.finrank Real E)` assumption. Focused verification and the targeted module build
passed. This restores an existing producer without restoring the obsolete conjugating-flow
implementation that qinz replaced.

Date: 2026-06-13. Verification: focused `lake env lean` PASSED (exit 0), no `sorry`.

## What this file provides

Part of filling `ham3_short_isSolution` (see
`Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.md`).  It supplies the
reusable bundle-continuity infrastructure that the realized tree was missing.

1. `tensor0SFamilyContinuousOnSet_of_chartComp` — **Keystone A**: the converse of
   `Tensor0SFamilyContinuousOnSet.eval_continuous`.  Builds joint total-space
   continuity of a `(0,s)` tensor family over `{t∈K}×M` from the continuity of
   its components against the local trivialization frame
   `(trivializationAt E (TangentSpace I) x₀).symmL ℝ q.2 (chartModelBasis (idx k))`,
   on each trivialization domain.

2. `tensor0SFamilyContinuousOnSet_of_chartBasisComp` — the keystone restated in the
   canonical chart-basis frame `chartBasisVecFiber` (defeq to the `symmL` frame, via
   `congr 1`).  This is the clean interface curvature consumers plug into: reduce
   `Tensor0SFamilyContinuousOnSet s K A` to "the chart-basis components
   `q ↦ A q.1.1 q.2 (chartBasisVecFiber x₀ (idx ·) q.2)` are jointly continuous on the
   trivialization domain".

3. `metricTensorCont_of_chartGram` — first consumer: from joint chart-Gram
   continuity produces `Tensor0SFamilyContinuousOnSet 2 K (metricTensorField (g ·))`
   (the `metricTensor_cont` field of `MetricFamilySmoothOn`/`IsSolutionOn`).  Routes
   through `_of_chartBasisComp`; the component reduces to `chartGramMatrix` by
   `metricTensorField_apply` + `chartGramMatrix_apply`.

## Key facts used (verified)

- `FiberBundle.continuousAt_totalSpace`: total-space continuity ⟺ base continuity
  ∧ fibre-coordinate continuity.
- Fibre coordinate of the `(0,s)` tensor bundle at `⟨b, A⟩` is
  `A.compContinuousLinearMap (fun _ => symmL x₀ b)` — DEFINITIONAL (`rfl`).
- `eval0SCLE n : Tensor0SModel n ℝ E ≃L[ℝ] ((Fin n → Fin (finrank ℝ E)) → ℝ)`
  (`DifferentialGeometry.Analysis.Parabolic.TensorSpectral`, in
  `RSTensor/Coordinates/TensorRSModelEvalBasis.lean`) is the finite-dim
  evaluation homeomorphism; `eval0SCLE_apply Φ φ = Φ (chartModelBasis ∘ φ)` is
  `rfl`.  Composing the fibre coordinate with this homeomorphism turns its
  continuity into per-component continuity (`continuousAt_pi`).
- `ContinuousMultilinearMap.compContinuousLinearMap_apply` (NOT rfl; needs `rw`).
- `symmL`'s `toFun` is `e.symm b` (Mathlib `Trivialization.symmL`); together with
  `chartBasisVecFiber x₀ i x := (triv x₀).symm x (chartModelBasis i)` this makes
  `symmL ℝ x (chartModelBasis i) = chartBasisVecFiber x₀ i x` close by `rfl` at
  default transparency (a `rw`-level rfl did NOT close it — used an explicit
  `funext; rfl` step).

## Gotchas / lessons

- **InnerProductSpace, not NormedSpace.**  `chartModelBasis`/`eval0SCLE` need the
  Euclidean structure (`[InnerProductSpace ℝ E]`).  Putting these lemmas in
  `MetricFamily.lean` (whose section has a free `[NormedSpace ℝ E]`) caused a
  `NormedSpace` instance DIAMOND (InnerProductSpace extends NormedSpace).  Fix:
  new file with its own `[InnerProductSpace Real E]` section — no free
  `NormedSpace`, so a single instance path.  All realized Ricci-flow consumers
  (`HamiltonPositiveRicci`, metric machinery) are already in `InnerProductSpace`.
- Normalise the `continuousAt_totalSpace` goal with `show … q₀.2 …` so the
  trivialization centre `(f q₀).proj` and the point `mk' … = ⟨q.2, …⟩` reduce to
  the clean form before working with the fibre coordinate.
- The local-frame validity (`baseSet`) is handled by `ContinuousOn` on the open
  nbhd `{q | q.2 ∈ baseSet x₀}`; the component identity itself is `rfl` regardless
  of `baseSet`, so no global frame field is needed.

## KEY FINDING (2026-06-13): joint curvature continuity is ALREADY built

The `ricciCont`/`rm04Cont` step is NOT an analytic wall.  `ShortTimeAssembly/
RicciContinuityInMetricTime.lean` already contains a full `RicciContJointAux`
namespace with JOINT `(t,x)`-continuity machinery over `Sp ⊆ ℝ × M`:
`jointGram_continuousOn`, `jointInvGram_continuousOn`, `jointChristoffel_continuousOn`,
`jointRiemann_continuousOn` (line 701), and `jointRicci_continuousOn` (line 740) —
the last gives `ContinuousOn (fun q : ℝ×M => chartRicciTensor (g_DT q.1) α i k (extChartAt α q.2)) Sp`
from joint chart-Gram `iteratedFDeriv` (k≤2) continuity (`h0`/`h1`/`h2`) on the
good set.  There is also `moving_chartCoord_jointContinuousWithinAt` (line 817).

So `ricciCont`/`rm04Cont` are ASSEMBLY, not new analysis:
1. From the short-time joint C∞ chart-Gram on `Ioo × baseSet`, produce the `h0`/`h1`/`h2`
   joint `iteratedFDeriv` continuity inputs (bridge `chartGramMatrix`/ContMDiffOn ⟶
   `chartGramOnE`/`iteratedFDeriv` continuity).
2. Apply `jointRicci_continuousOn` / `jointRiemann_continuousOn` → joint chart-Ricci/Rm
   continuity.
3. Bridge joint `chartRicciTensor` → joint chart-frame Ricci components of `S.ricci`
   (the `ricciTensor_eq_chartRicciSwap_of_basis_identity` identity, joint version).
4. Apply `tensor0SFamilyContinuousOnSet_of_chartBasisComp` (this file) → `ricciCont`.
This couples to the short-time family + the `chartGramOnE`/`chartRicci` shapes — a
focused assembly session, now clearly feasible (no wall).

## 2026-06-13 KEYSTONE GENERALIZED + Ricci chart-frame bridge built

- `tensor0SFamilyContinuousOnSet_of_chartComp`/`…_of_chartBasisComp` now take an explicit
  neighbourhood family `(N : M → Set M) (hN : ∀ x₀, N x₀ ∈ nhds x₀)` instead of hardcoding
  `baseSet`.  `hopen` uses `continuous_snd.continuousAt.preimage_mem_nhds (hN q₀.2)`.  The metric
  consumer passes `N = baseSet`; curvature consumers pass `N = chartLeviCivitaGoodSet` (open, and
  `self_mem_chartLeviCivitaGoodSet`), which is where the chart-frame Ricci identity holds.
- `ricciChartFrameComp_jointContinuousOn` (in `RicciContinuityInMetricTime.lean`) gives joint
  continuity of `ricciTensor (g_DT q.1) q.2 (cbvf α i q.2)(cbvf α j q.2)` on `Sp` (good-set), via
  `ricciTensor_chartBasisVec_alpha_eq` `.congr`'d through `chartRicci_jointContinuousOn`.

### BLOCKER for the `ricciCont` consumer: missing `metricRicciAt = ricciTensor` API

`ricciCont` is `Tensor0SFamilyContinuousOnSet 2 (S.ricci)`, and `S.ricci t x = S.ricciAt t x =
metricRicciAt (g t) x`.  To apply `…_of_chartBasisComp` (with `N = goodSet`), its component
`metricRicciAt (g q.1) q.2 (fun k => cbvf α (idx k) q.2)` must equal
`ricciTensor (g q.1) q.2 (cbvf α (idx 0))(cbvf α (idx 1))` — i.e. the bridge
`metricRicciAt g x (vec2 v w) = ricciTensor g x v w`.  **This lemma does NOT exist in-tree.**
`metricRicciAt g x = ricciFromRm13At (riemannCurvatureAt (metricCov g) x)`
(`Curvature/Metric.lean:75`, `Riemann/Basic/Pointwise.lean:657`), while
`ricciTensor g x v w = trace (ricciEndo g x v w)` (`CurvatureOperator/RicciConnection.lean:232`,
`ricciEndo` via `riemannOp (LeviCivita g)`).  So the bridge is a genuine curvature-contraction
identity (`ricciFromRm13At`-contraction = `trace`, plus `metricCov g ↔ LeviCivita g`), not a clean
unfold — its own focused proof (likely via `ricciCompAt`/`RicciTrace.lean` component matching +
tensor ext).

**DEEPER (2026-06-13): the bridge needs reconciling TWO Levi-Civita constructions.**
`ricciTensor` (RicciConnection.lean) is built on `LeviCivita g` — the *stitched-from-chart-good-set*
connection (`Connection/LeviCivita/Defs.lean:249`, `CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover`
over `leviCivitaStitched`).  `metricRicciAt`/`S.ricci` is built on `metricCov g =
leviCivitaConnectionOfMetric g` (a *direct* construction).  NO reconciliation lemma
`LeviCivita g = leviCivitaConnectionOfMetric g` (or curvature agreement) exists in-tree.  So the
bridge prerequisite is: (1) the two LC constructions agree (LC uniqueness: both are metric-compatible
torsion-free, e.g. `IsLeviCivita (leviCivitaConnectionOfMetric g) g` is proven in `Torsion.lean:406`,
but the uniqueness `IsLeviCivita cov g → cov = LeviCivita g` is not wired to this), AND (2) the
contraction-vs-trace identity.  This is a deep curvature-algebra sub-project.

**UPDATE (2026-06-13): the reconciliation route EXISTS but is blocked by a typeclass bind.**
The connection-level reconciliation `leviCivitaConnectionOfMetric g ≡ LeviCivita g` (on
differentiable sections) is provable: `LeviCivita_unique` (`Connection/LeviCivita/Defs.lean:359`,
wrapping `koszul_levi_civita_unique_of_torsionFree_metricCompatible`, `Connection/LeviCivita/Koszul.lean:217`)
takes any torsion-free metric-compatible `cov` and shows `cov.toFun σ x v = (LeviCivita g).toFun σ x v`;
`leviCivitaConnectionOfMetric` supplies both via `leviCivitaConnectionOfMetric_isLeviCivita`
(`Torsion.lean:404`) — `.2 : IsTorsionFree` gives `torsion = 0` by `funext` (since
`IsTorsionFreeAt cov x := cov.torsion x = 0`), and `leviCivitaConnectionOfMetric_isMetricCompatible`
gives metric-compatibility.

BUT a one-file reconciliation lemma hit a TYPECLASS-ELABORATION BIND (attempted in a deleted
`Connection/LeviCivita/Reconcile.lean`; 7 failed instance configurations → hit the 3-mistake stop):
the two LC worlds have incompatible instance setups.
- The signature's `g : SmoothRiemannianMetric I M` + `MDiffAt (T% σ) x` (tangent-bundle
  `ChartedSpace`) synthesizes cleanly under `[NormedSpace ℝ E]`, but then
  `leviCivitaConnectionOfMetric_isLeviCivita`/`_isMetricCompatible` demand `[InnerProductSpace ℝ E]`.
- Switching to `[InnerProductSpace ℝ E]` (which provides `NormedSpace`, avoiding a diamond) makes
  those facts resolve, but then the tangent-bundle `ChartedSpace (ModelProd H (ModelProd H E))
  (TotalSpace E (TangentSpace I))` synthesis for `MDiffAt (T% σ)` FAILS (a spurious double-`ModelProd`,
  even with `[NeZero (Module.finrank ℝ E)]` matching the working `RicciContinuityInMetricTime` block).
Classification: typeclass/instance-elaboration obstruction (not math). The fix is a design-level
reconciliation of the instance requirements of the `LeviCivita`-stitched world (NormedSpace +
`Defs` block: SigmaCompact/T2/Boundaryless) vs the `leviCivitaConnectionOfMetric` world
(InnerProductSpace + Torsion/KoszulFormula block) — likely a small `variable` setup that satisfies
both, found by inspecting how a future file imports the two together, or by weakening the lcOfMetric
facts' `InnerProductSpace` requirement to `NormedSpace` (the `g.inner` is on tangent spaces, so it
may not genuinely need `E` itself to be inner-product). This is a planner/design decision.

With the bridge (connection agreement) + its curvature/Ricci lift, the `ricciCont`
consumer is:
`_of_chartBasisComp (N := goodSet) … ` rewriting the component by the bridge, then
`ricciChartFrameComp_jointContinuousOn` (modulo the `ℝ×M`↔subtype conversion + short-time jets).

## Next (remaining bricks for ham3_short_isSolution)

See `HamiltonPositiveRicci.md` (2026-06-13 sections).  Summary: SMOOTH keystone
analog → `coeff`/`frameCompSmooth`; `coeff_cont` from this file's consumer;
`smoothConnection`/`equation` direct; Ricci/Rm/scalar continuity via the keystone
fed curvature-component joint continuity on the interior slab; assemble
`isSolutionOn_interior_slab`; bridge to `ham3_short_isSolution` by recentering.

## 2026-06-13 BLOCKER RESOLVED: the two-LC reconciliation now compiles

The `metricRicciAt = ricciTensor` blocker above (two unreconciled Levi-Civita constructions) is
no longer a wall.  `Connection/LeviCivita/Reconcile.lean` (NEW, verified exit 0, no sorry):
`leviCivitaConnectionOfMetric_apply_eq_leviCivita` proves the two LC constructions AGREE on
differentiable sections, via `LeviCivita_unique` (Koszul uniqueness).  The earlier "typeclass bind"
was a misdiagnosis: the fix (user's casting/instance insight) is to declare BOTH `[NormedSpace ℝ E]`
and `[InnerProductSpace ℝ E]` — the codebase's coherent convention (`Defs.lean:77-78`) — plus
`[NeZero (Module.finrank ℝ E)]`, and convert `IsMetricCompatible_gen`→`IsMetricCompatible` inline.
See `Connection/LeviCivita/Reconcile.md`.

So `ricciCont`'s remaining steps are now: (i) lift the connection agreement to
`metricRicciAt g x (vec2 v w) = ricciTensor g x v w` (push through the curvature formula on smooth
sections); (ii) apply `tensor0SFamilyContinuousOnSet_of_chartBasisComp (N := goodSet)` to `S.ricci`
(= `metricRicciAt (g t)`), rewriting the chart-frame component via (i), then
`ricciChartFrameComp_jointContinuousOn`.  No analytic/typeclass wall remains — (i) is a
curvature-algebra lift and (ii) is mechanical.

## 2026-07-01: `Tensor0SFamilyContinuousOnSet.pullback` (P1.4 bundle-section pullback transport)

NEW, verified sorry-free (targeted build 3490 jobs).  In the `Tensor0SFamilyContinuousOnSet`
namespace: for `hA : Tensor0SFamilyContinuousOnSet (M := N) s K A` and `Φ : M ≃ₘ⟮I,I⟯ N`,
the Φ-pullback `(t, x) ↦ (A t (Φ x)).compContinuousLinearMap (fun _ => mfderiv I I Φ x)` is jointly
continuous over `{t∈K}×M`.  THIS is the keystone P1.4 needed (last session's "bundle-section pullback
frontier" — the survey had MISSED that the converse builder `…_of_chartBasisComp` already exists here;
with it the lemma is ~30 lines).

Route (mirrors the metric consumer): `apply tensor0SFamilyContinuousOnSet_of_chartBasisComp` with
`N := baseSet`; per `(x₀, idx)`, `continuousOn_iff_continuous_restrict` to the subtype
`{q // q.2 ∈ baseSet x₀}`; then `hA.eval_continuous` with `τ q := q.1.1.1`, `b q := Φ q.1.2`,
slot `v k q := mfderiv I I Φ q.1.2 (chartBasisVecFiber x₀ (idx k) q.1.2)`.  Slot continuity (`hv`):
the pushed chart-basis section equals `tangentMap I I Φ ∘ (fun q => chartBasisVec x₀ (idx k) q.1.2)`
(by `rfl` — `tangentMap f ⟨y,w⟩ = ⟨f y, mfderiv f y w⟩` = `mk'`), continuous via
`(Φ.contMDiff.continuous_tangentMap (by simp)).comp` of `chartBasisVec_contMDiffOn x₀ (idx k)
|>.continuousOn.comp_continuous … (fun p => p.2)`.  Final `hev.congr` + `simp only [Set.restrict_apply,
ContinuousMultilinearMap.compContinuousLinearMap_apply]`.

Consumed in `HCGCompactness/SolutionPullback.lean` for `metricTensor_cont` (via `metricTensorField_apply`
+ `pullbackMetric_inner`), `ricciCont` (via `metricRicci_pullback_eval`), `rm04Cont` (via
`metricRm04_pullback_eval`).  See SolutionPullback.md.

## 2026-07-02: `Tensor0SFamilyContinuousOnSet.restrictOpen` (Brick 1 open-inclusion transport)

NEW, verified sorry-free (targeted build).  Restriction-analog of `.pullback` along the open inclusion
`Subtype.val : U → M` (`U : Opens M`): for `hA : Tensor0SFamilyContinuousOnSet (M := M) s K A`, the
restriction `(t, x:U) ↦ A t ↑x` is jointly continuous over `{t∈K}×U`.  Same route as `.pullback` but
`_of_chartBasisComp` on the SOURCE `U`, base `↑x`, slots pushed by `mfderiv Subtype.val` (= id, via
`mfderiv_subtype_val_apply`); the pushed chart-basis section is `tangentMap Subtype.val ∘ chartBasisVec`.
Two deltas vs `.pullback`: (1) pin `contMDiff_subtype_val (n := ∞)` for `continuous_tangentMap (by simp)`
(else `n` is a metavar `by simp` can't discharge); (2) the final goal reduces to `A .. (fun i =>…) =
A .. (fun k =>…)` (alpha) which `simp only [Set.restrict_apply, mfderiv_subtype_val_apply]` does NOT
close — needs a trailing `rfl`.  Carries U-instances as hypotheses
`[SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] [IsManifold I ((∞)+1) U]`.  Adds one import
`Geometry/Metric/OpenSubtype` (for `mfderiv_subtype_val_apply`; no cycle).  Consumed in
`HCGCompactness/SolutionRestrictOpen.lean` for `metricTensor_cont`/`ricciCont`/`rm04Cont`.
