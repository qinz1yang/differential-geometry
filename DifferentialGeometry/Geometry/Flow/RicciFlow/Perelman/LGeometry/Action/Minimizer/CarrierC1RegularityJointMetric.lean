import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.Sobolev
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Regularity.CarrierC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.StrictRefinement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1RegularityAbsolutelyContinuous
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothnessScalar
set_option autoImplicit false

noncomputable section

open Set Bundle MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace.PseudoMetrizableSpace M] {D : RealTimeInterval}

theorem lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a < b) (gamma : ℝ → M)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume a b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ Ioo a b, T - r ^ 2 ∈ D.regular)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (U ×ˢ (univ : Set M)))
    (hmin : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b) := by
  apply lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives
    S hS T a b hab gamma hgamma hint U hU htime hreg _ _ hmin
  · intro p
    apply chartGramOp_spatial_fderiv_continuousOn S.family p
      (fun _ hz => interior_subset hz.2)
    intro i j
    have hh := chartGramOnE_contDiffOn_of_contMDiffOn S.base.metric hmetric p i j
    exact (hh.iteratedFDeriv_snd
      (G := fun t y => chartGramOnE (S.base.metric t) p i j y)
      isOpen_interior 1 (m := 0) (by simp)).continuousOn
  · intro p
    exact chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn S.base.metric hmetric p

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
