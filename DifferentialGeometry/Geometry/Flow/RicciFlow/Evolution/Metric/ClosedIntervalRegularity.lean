import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.Continuity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Bundle _root_.Manifold Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem solution_metric_tensor_contMDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.base.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc c b ×ˢ (univ : Set M)) := by
  exact solution_metricCLMSection_contMDiffOn_closed S hS hac hcb hslab hregular

end DifferentialGeometry.PDE.RicciFlow
