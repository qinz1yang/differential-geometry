import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalCoorientation
import DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalDerivative
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

open private cylinderAxialDerivative_continuousOn from DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalDerivative

theorem exists_constant_axial_sign
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, (A (p, 0)).2 = 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ p : S2, σ * deriv (fun t => (A (p, t)).2) 0 > 0 := by
  classical
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  let d : S2 → ℝ := fun p => deriv (fun t => (A (p, t)).2) 0
  have hd : Continuous d := by
    let f : SphereCylinder → ℝ := fun q => deriv (fun t => (A (q.1, t)).2) q.2
    let j : S2 → SphereCylinder := fun p => (p, 0)
    have hj : Continuous j := continuous_id.prodMk continuous_const
    have hF : ContinuousOn f A.source := cylinderAxialDerivative_continuousOn A
    exact continuousOn_univ.mp (hF.comp hj.continuousOn (fun p _ => hsource p))
  have hne : ∀ p, d p ≠ 0 := fun p => axial_derivative_ne_zero_of_zero_section A hsource hzero p
  by_cases hp : ∀ p : S2, 0 < d p
  · exact ⟨1, Or.inl rfl, fun p => by simpa [d] using hp p⟩
  · push Not at hp
    obtain ⟨q, hq⟩ := hp
    have hqneg : d q < 0 := lt_of_le_of_ne hq (hne q)
    have hn : ∀ p : S2, d p < 0 := by
      intro p
      by_contra hp
      have hp0 : 0 ≤ d p := le_of_not_gt hp
      obtain ⟨z, hz⟩ := intermediate_value_univ q p hd ⟨hqneg.le, hp0⟩
      exact hne z hz
    exact ⟨-1, Or.inr rfl, fun p => by change 0 < -1 * d p; nlinarith [hn p]⟩

end DifferentialGeometry.Topology.Manifold
