import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Multilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M]

private local instance closedMetricFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem metricTensor_contDiffOn_time
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (x : M) :
    ContDiffOn ℝ ∞ (fun t => metricTensorField (S.base.metric t) x) (Icc c b) := by
  classical
  obtain ⟨V, hV, hxV, hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed S hS hac hcb hslab hreg x
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  let basis := chartBasisFamily (I := I) x hx
  have hc (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => component0S (I := I) basis (metricTensorField (S.base.metric t) x) slots)
        (Icc c b) := by
    have hm := (hgram (slots 0) (slots 1)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hxV⟩)
    apply hm.congr
    intro t _ht
    simp only [Function.comp_def, id_eq, component0S_apply, metricTensorField_apply,
      basis, chartBasisFamily_apply, chartGramOnE, chartGramMatrix_apply]
    erw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  have hsum : ContDiffOn ℝ ∞
      (fun t => ∑ slots, component0S (I := I) basis (metricTensorField (S.base.metric t) x) slots •
        tensor0SBasis (I := I) basis 2 slots) (Icc c b) :=
    ContDiffOn.sum fun slots _ => (hc slots).smul_const _
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

private theorem metric_timeJet_eval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c b) (x : M) (v : Fin 2 → TangentSpace I x) :
    iteratedDerivWithin q (fun s => (S.base.metric s).inner x (v 0) (v 1)) (Icc c b) t =
      (iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t) v := by
  have hq : (q : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hh := (tensor0SEvalCLM (I := I) v).iteratedFDerivWithin_comp_left
    (metricTensor_contDiffOn_time S hS hac hcb hslab hreg x t ht)
    (uniqueDiffOn_Icc hcb) ht hq
  have he := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin q => ℝ) ℝ =>
    A (fun _ => 1)) hh
  exact he

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem exists_field_of_chart_components
    (T : (x : M) → Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x)
    (hT : ∀ p : M, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) ∞
        (fun x => T x (fun k => chartBasisVecFiber (I := I) p (slots k) x)) p) :
    ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) 2, ∀ x, B x = T x := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (I := I) (M := M) 2
  refine ⟨⟨T, ?_⟩, fun _ => rfl⟩
  let basis := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ basis T).mpr ?_
  intro slots p
  refine (hT p slots).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  let e := trivializationAt E (TangentSpace I) p
  have hrepr := continuousMultilinearMap_basis_repr (𝕜 := ℝ) basis 2
    ((trivializationAt (Tensor0SModel 2 ℝ E)
      (Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I)) p) ⟨x, T x⟩).2 slots
  refine hrepr.trans ?_
  change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) 2 x (T x)).compContinuousLinearMap
    (fun _ : Fin 2 => e.symmL ℝ x) (fun k => basis (slots k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact tensor0SSpaceFiberContinuousLinearEquiv_apply_apply (I := I) 2 x (T x)
    (fun k => chartBasisVecFiber (I := I) p (slots k) x)

private theorem exists_metric_timeJet_field
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c b) :
    ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) 2,
      ∀ x, B x = iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t := by
  let T := fun x => iteratedDerivWithin q
    (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t
  apply exists_field_of_chart_components T
  intro p slots
  obtain ⟨V, hV, hpV, hVt, hjets⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed S hS hac hcb hslab hreg p
  have hmaps : MapsTo (fun y : E => (t, y)) V (Icc c b ×ˢ V) := fun _ hy => ⟨ht, hy⟩
  have hcoord : ContDiffOn ℝ ∞ (fun y => iteratedDerivWithin q
      (fun s => chartGramOnE (I := I) (S.base.metric s) p (slots 0) (slots 1) y)
      (Icc c b) t) V :=
    (hjets q (slots 0) (slots 1)).comp (f := fun y : E => (t, y))
      (contDiffOn_const.prodMk contDiffOn_id) hmaps
  have hlocal : ContMDiffAt I 𝓘(ℝ) ∞ (fun x : M => iteratedDerivWithin q
      (fun s => chartGramOnE (I := I) (S.base.metric s) p (slots 0) (slots 1)
        (extChartAt I p x)) (Icc c b) t) p :=
    (hcoord.contDiffAt (hV.mem_nhds hpV)).contMDiffAt.comp p
      (contMDiffAt_extChartAt (I := I) (x := p))
  refine hlocal.congr_of_eventuallyEq ?_
  let e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  filter_upwards [e.open_baseSet.mem_nhds hp] with x hx
  change (iteratedDerivWithin q (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t)
    (fun k => chartBasisVecFiber (I := I) p (slots k) x) = _
  rw [← metric_timeJet_eval S hS hac hcb hslab hreg q ht x
    (fun k => chartBasisVecFiber (I := I) p (slots k) x)]
  have hxs : x ∈ (extChartAt I p).source := by
    simpa only [e, trivializationAt_baseSet_eq_chartAt_source, extChartAt_source_eq_chartAt_source]
      using hx
  apply congrArg (fun f : ℝ → ℝ => iteratedDerivWithin q f (Icc c b) t)
  funext s
  simp only [chartGramOnE, chartGramMatrix_apply, (extChartAt I p).left_inv hxs]


theorem exists_closedWindow_metric_time_fields
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField (S.base.metric t)) ∧
      ∀ q t, t ∈ Icc c b → ∀ x,
        B q t x = iteratedDerivWithin q
          (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t ∧
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (Icc c b) t := by
  classical
  choose C hC using fun q (t : Icc c b) =>
    exists_metric_timeJet_field S hS hac hcb hslab hreg (q + 1) t.property
  let B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (S.base.metric t)
    | q + 1 => if ht : t ∈ Icc c b then C q ⟨t, ht⟩ else 0
  have hB (q : ℕ) (t : ℝ) (ht : t ∈ Icc c b) (x : M) :
      B q t x = iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) x) (Icc c b) t := by
    cases q with
    | zero => simp only [B, iteratedDerivWithin_zero]
    | succ q => simpa only [B, dif_pos ht] using hC q ⟨t, ht⟩ x
  refine ⟨B, fun _ => rfl, ?_⟩
  intro q t ht x
  refine ⟨hB q t ht x, ?_⟩
  have hq : (q : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top q)
  have hf := metricTensor_contDiffOn_time S hS hac hcb hslab hreg x
  have hd := (hf.differentiableOn_iteratedDerivWithin hq (uniqueDiffOn_Icc hcb) t ht).hasDerivWithinAt
  rw [← iteratedDerivWithin_succ] at hd
  exact (hd.congr_deriv (hB (q + 1) t ht x).symm).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => hB q s hs x) (hB q t ht x)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
