import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsLRegularizedGeodesicOn.congr_of_eventuallyEq
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {alpha beta : ℝ → M} {J : Set ℝ}
    (ha : IsLRegularizedGeodesicOn S T alpha J)
    (heq : ∀ r ∈ J, beta =ᶠ[𝓝 r] alpha) :
    IsLRegularizedGeodesicOn S T beta J := by
  intro r hr
  have heq := heq r hr
  have hvel : ∀ᶠ t in 𝓝 r,
      lVelocity (I := I) beta t = lVelocity (I := I) alpha t := by
    filter_upwards [heq.eventuallyEq_nhds] with t ht
    unfold lVelocity
    rw [ht.mfderiv_eq]
    rfl
  have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
    (fun t => lVelocity (I := I) beta t) (fun t => lVelocity (I := I) alpha t)
    heq hvel
  have hacc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (S.base.metric (T - r ^ 2))
    (fun t => lVelocity (I := I) beta t) (fun t => lVelocity (I := I) alpha t)
    heq hvel
  have h := ha r hr
  refine ⟨h.1, h.2.1.congr_of_eventuallyEq heq, ?_, ?_⟩
  · exact h.2.2.1.congr_of_eventuallyEq hrep
  · rw [hacc, h.2.2.2, heq.eq_of_nhds, hvel.self_of_nhds]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
