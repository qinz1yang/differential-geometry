import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.EndpointConvergence
import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.Continuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem tendsto_forwardUniqueDensity_zero_of_complete_bounded_curvature
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁) (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂) {a b C₁ C₂ : ℝ} (hab : a < b)
    (hcarrier₁ : Icc a b ⊆ D₁.carrier) (hcarrier₂ : Icc a b ⊆ D₂.carrier)
    (hregular₁ : Ioc a b ⊆ D₁.regular) (hregular₂ : Ioc a b ⊆ D₂.regular)
    (hcomplete₁ : RiemannianMetricComplete (I := I) (S₁.base.metric a))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcurv₁ : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ C₁)
    (hcurv₂ : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ C₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) (x : M) :
    Tendsto (fun t => forwardUniqueDensity S₁.base.metric S₂.base.metric t x)
      (𝓝[Ioo a b] a) (𝓝 0) := by
  have hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a) := by
    rw [← hinit]
    exact hcomplete₁
  apply tendsto_forwardUniqueDensity_zero_of_connectionDifferenceSq_tendsto
    S₁ S₂ hS₁ hS₂ hab hcarrier₁ hcarrier₂ hinit x
  apply tendsto_connectionDifferenceSq_zero_of_chartChristoffel
    S₁.base.metric S₂.base.metric (S₁.base.metric a) x
  · intro i j
    have hcont := (hS₁.smoothMetric.coeff_cont x
      (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))
        a (hcarrier₁ (left_mem_Icc.mpr hab.le))
    simpa only [chartGramMatrix_apply, SolutionOn.family_metric] using (hcont.mono
      (Ioo_subset_Icc_self.trans hcarrier₁)).tendsto
  · exact tendsto_chartChristoffel_left_endpoint_of_complete_bounded_curvature
      S₁ hS₁ hab hcarrier₁ hregular₁ hcomplete₁ hC₁ hcurv₁ x
  · intro i j k
    have h := tendsto_chartChristoffel_left_endpoint_of_complete_bounded_curvature
      S₂ hS₂ hab hcarrier₂ hregular₂ hcomplete₂ hC₂ hcurv₂ x i j k
    simpa only [SolutionOn.family_metric, hinit] using h

end DifferentialGeometry.PDE.RicciFlow

end
