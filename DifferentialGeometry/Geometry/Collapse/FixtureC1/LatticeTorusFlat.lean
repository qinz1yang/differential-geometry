import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusMetric
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

/-!
# The flat torus has vanishing curvature (S-FIXTURE-C1, K1, file 8)

`torMetric_sectional_FXC1`: `SectionalBoundedBelowAt (torMetric_FXC1 Λ) y K` for every `K ≤ 0`
(`sec = 0`): the Riemann tensor of `torMetric` pulls back along the local isometry `torPi` to the
Riemann tensor of the Euclidean metric, which vanishes (`metricRm04StandardAt_localPullMetric`).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The Riemann tensor of the flat torus vanishes. -/
theorem torMetric_rm04_FXC1 (Λ : TorusPeriods_FXC1) (y : Tor_FXC1 Λ)
    (v w : TangentSpace 𝓘(ℝ, E3) y) :
    metricRm04StandardAt (torMetric_FXC1 Λ) y v w w v = 0 := by
  obtain ⟨x, rfl⟩ := torPi_surjective_FXC1 Λ y
  let hD := (torPi_isLocalDiffeomorph_FXC1 Λ).mfderivToContinuousLinearEquiv (n := ∞)
    (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hcoe : (hD : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] TangentSpace 𝓘(ℝ, E3) (torPi_FXC1 Λ x)) =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) x :=
    (torPi_isLocalDiffeomorph_FXC1 Λ).mfderivToContinuousLinearEquiv_coe (n := ∞)
      (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hv : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) x (hD.symm v) = v := by
    rw [← hcoe]; exact hD.apply_symm_apply v
  have hw : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) x (hD.symm w) = w := by
    rw [← hcoe]; exact hD.apply_symm_apply w
  have h := metricRm04StandardAt_localPullMetric (torMetric_FXC1 Λ) (torPi_FXC1 Λ)
    (torPi_isLocalDiffeomorph_FXC1 Λ) x (hD.symm v) (hD.symm w) (hD.symm w) (hD.symm v)
  rw [hv, hw, torMetric_localPull_FXC1] at h
  rw [← h]
  simp only [metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero]
  rfl

/-- **`sec = 0`**: the flat torus is bounded below by every nonpositive constant. -/
theorem torMetric_sectional_FXC1 (Λ : TorusPeriods_FXC1) (y : Tor_FXC1 Λ) {K : ℝ} (hK : K ≤ 0) :
    SectionalBoundedBelowAt (torMetric_FXC1 Λ) y K := by
  have h0 : SectionalBoundedBelowAt (torMetric_FXC1 Λ) y 0 := by
    intro v w
    rw [zero_mul, torMetric_rm04_FXC1 Λ y v w]
  exact h0.mono hK

end DifferentialGeometry.Geometry.Collapse
