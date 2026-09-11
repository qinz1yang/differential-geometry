import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Bundle Set DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

section MetricCoefficients

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem chartGramMatrix_continuousOn_carrier
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : {t : ℝ // t ∈ D.carrier} × M ↦
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g q.1.1) x₀ q.2 i j)
      {q : {t : ℝ // t ∈ D.carrier} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hslot : ∀ k : Fin 2, Continuous
      (fun p : {q : {t : ℝ // t ∈ D.carrier} × M //
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) p.1.2
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (if k = 0 then i else j) p.1.2)) := by
    intro k
    exact (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) x₀
      (if k = 0 then i else j)).continuousOn.comp_continuous
        (continuous_snd.comp continuous_subtype_val) (fun p ↦ p.2)
  have hev := hG.metricTensor_cont.eval_continuous
    (P := {q : {t : ℝ // t ∈ D.carrier} × M //
      q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
    (τ := fun p ↦ p.1.1.1) (b := fun p ↦ p.1.2)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    (fun p ↦ p.1.1.2) (continuous_snd.comp continuous_subtype_val) hslot
  refine hev.congr ?_
  intro p
  change metricTensorField (g p.1.1.1) p.1.2
    (fun k : Fin 2 ↦ DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀
      (if k = 0 then i else j) p.1.2) =
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1.1.1) x₀ p.1.2 i j
  rw [metricTensorField_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  rfl

end MetricCoefficients

section GramOperator

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem chartGramOp_continuousOn_carrier
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) (x₀ : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I x₀).target) :
    ContinuousOn (chartGramOp (I := I) G x₀) (J ×ˢ K) := by
  classical
  let P := {q : ℝ × E // q ∈ J ×ˢ K}
  let base : P → M := fun q ↦ (extChartAt I x₀).symm q.1.2
  have hbase : Continuous base :=
    (continuousOn_extChartAt_symm (I := I) x₀).comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun q ↦ interior_subset (hK q.2.2))
  have hbaseSet : ∀ q : P,
      base q ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro q
    have hsource := (extChartAt I x₀).map_target (interior_subset (hK q.2.2))
    change (extChartAt I x₀).symm q.1.2 ∈ (chartAt H x₀).source
    rwa [← extChartAt_source (I := I) (H := H) x₀]
  let lift : P → {t : ℝ // t ∈ D.carrier} × M :=
    fun q ↦ (⟨q.1.1, hJ q.2.1⟩, base q)
  have hlift : Continuous lift :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk hbase
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun q : ℝ × E ↦ chartGramOnE (I := I) (G.metric q.1) x₀ i j q.2)
        (J ×ˢ K) := by
    intro i j
    rw [continuousOn_iff_continuous_domRestrict]
    exact (chartGramMatrix_continuousOn_carrier G.metric hG x₀ i j).comp_continuous
      hlift hbaseSet
  let : IsTopologicalAddGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.topologicalAddGroup
  let : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.topologicalAddGroup
  let : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.topologicalAddGroup (E := E) (F := E →L[ℝ] ℝ)).toContinuousAdd
  have hbilin : ContinuousOn
      (fun q : ℝ × E ↦ chartGramBilin (E := E) (I := I) (M := M)
        (G.metric q.1) x₀ ((extChartAt I x₀).symm q.2)) (J ×ˢ K) := by
    change ContinuousOn
      (fun q : ℝ × E ↦
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) (G.metric q.1) x₀ i j q.2 •
            (chartCoordCLM E i).smulRight (chartCoordCLM E j)) (J ×ˢ K)
    exact continuousOn_finsetSum _ fun i _ ↦
      continuousOn_finsetSum _ fun j _ ↦ (hentry i j).smul continuousOn_const
  exact (IsCoercive.gramCLM (F := E)).continuous.comp_continuousOn hbilin

end GramOperator

end DifferentialGeometry.PDE.RicciFlow

end
