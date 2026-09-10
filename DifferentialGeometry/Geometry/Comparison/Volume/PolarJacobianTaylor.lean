import DifferentialGeometry.Geometry.Comparison.Volume.PolarJacobianJets
import DifferentialGeometry.Geometry.Comparison.Volume.PolarTaylorRemainder

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_radial_jets
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) (u : E) :
    iteratedDeriv 1
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 = 0 ∧
      iteratedDeriv 2
        (fun t : ℝ ↦ normalExpJacobian (I := I) g hEnorm p (t • u)) 0 =
        -(1 / 3 : ℝ) * ricciTensor (I := I) g p
          (normalFrame (I := I) g p u)
          (normalFrame (I := I) g p u) := by
  exact normalExpJacobian_radial_jets_of_intrLaunchJet_two_zero
    (I := I) g hEnorm p u
    (fun a b ↦ intrinsicLaunchJet_two_zero (I := I) g hEnorm p a b)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_uniform_taylor_remainder
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Metric.sphere (0 : E) 1) (t : ℝ),
        t ∈ Set.Icc 0 ρ →
          |normalExpJacobian (I := I) g hEnorm p (t • (u : E)) -
            (1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
              (normalFrame (I := I) g p (u : E))
              (normalFrame (I := I) g p (u : E)) * t ^ 2)| ≤
            C * t ^ 3 := by
  apply normalExpJacobian_uniform_taylor_remainder_of_radial_jets
    (I := I) g hEnorm p
  intro u
  exact normalExpJacobian_radial_jets (I := I) g hEnorm p (u : E)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_uniform_taylor_remainder
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Metric.sphere (0 : E) 1) (t : ℝ),
        t ∈ Set.Icc 0 ρ →
          |normalPolarJacobian (I := I) g hEnorm p t u -
            t ^ (Module.finrank ℝ E - 1) *
              (1 - (1 / 6 : ℝ) * ricciTensor (I := I) g p
                (normalFrame (I := I) g p (u : E))
                (normalFrame (I := I) g p (u : E)) * t ^ 2)| ≤
            C * t ^ (Module.finrank ℝ E - 1) * t ^ 3 := by
  apply normalPolarJacobian_uniform_taylor_remainder_of_radial_jets
    (I := I) g hEnorm p
  intro u
  exact normalExpJacobian_radial_jets (I := I) g hEnorm p (u : E)

end Poincare.Geometry.Riemannian.VolumeComparison

end
