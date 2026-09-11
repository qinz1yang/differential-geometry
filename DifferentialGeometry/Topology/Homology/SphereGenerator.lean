import DifferentialGeometry.Topology.Homology.LiftedSphere



noncomputable section

universe u

namespace DifferentialGeometry.Topology





def IsSphereHomologyGenerator (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) : Prop :=
  ∃ e : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) ≃ₗ[ℤ] ℤ, e c = 1



theorem integralLiftedSphereGenerator_isGenerator (n : ℕ) :
    IsSphereHomologyGenerator n (integralLiftedSphereGenerator.{u} n) :=
  ⟨integralLiftedSphereTopEquiv n, integralLiftedSphereGenerator_coordinate n⟩


theorem IsSphereHomologyGenerator.ne_zero (n : ℕ)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHomologyGenerator n c) : c ≠ 0 := by
  obtain ⟨e, he⟩ := h
  intro hc
  rw [hc, map_zero] at he
  exact zero_ne_one he

end DifferentialGeometry.Topology
