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

theorem IsSphereHomologyGenerator.eq_or_eq_neg (n : ℕ)
    {c g : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (hc : IsSphereHomologyGenerator n c) (hg : IsSphereHomologyGenerator n g) :
    c = g ∨ c = -g := by
  obtain ⟨e, he⟩ := hc
  obtain ⟨e', he'⟩ := hg
  have hmul : e g • c = g := by
    have h : e (e g • c) = e g := by
      rw [map_zsmul, he]
      simp
    exact e.injective h
  have hkey : e g * e' c = 1 := by
    have h2 : e' (e g • c) = e g * e' c := by simp only [map_zsmul, smul_eq_mul]
    rw [hmul] at h2
    rw [← h2, he']
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hkey with h | h
  · left
    rw [← hmul, h, one_smul]
  · right
    rw [← hmul, h]
    simp

theorem isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n c ↔
      c = integralLiftedSphereGenerator.{u} n ∨ c = -integralLiftedSphereGenerator.{u} n := by
  constructor
  · intro hc
    exact IsSphereHomologyGenerator.eq_or_eq_neg n hc
      (integralLiftedSphereGenerator_isGenerator n)
  · rintro (rfl | h)
    · exact integralLiftedSphereGenerator_isGenerator n
    · rw [h]
      exact ⟨(integralLiftedSphereTopEquiv n).trans (LinearEquiv.neg ℤ), by
        simp [integralLiftedSphereGenerator_coordinate]⟩

end DifferentialGeometry.Topology
