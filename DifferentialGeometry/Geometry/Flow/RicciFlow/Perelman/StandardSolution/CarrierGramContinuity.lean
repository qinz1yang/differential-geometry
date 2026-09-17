import DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier
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
  exact DifferentialGeometry.Geometry.Curvature.chartGramOp_continuousOn_of_carrier
    hG hJ x₀ (hK.trans interior_subset)

end GramOperator

end DifferentialGeometry.PDE.RicciFlow

end
