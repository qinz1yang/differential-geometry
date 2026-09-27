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

theorem isSphereHomologyGenerator_iff_exists_surjective_functional (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n c ↔
      ∃ φ : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ,
        Function.Surjective φ ∧ φ c = 1 := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.toLinearMap, fun y => ⟨e.symm y, e.apply_symm_apply y⟩, he⟩
  · rintro ⟨φ, hφ, hc⟩
    set ψ : ℤ →ₗ[ℤ] ℤ := φ.comp (integralLiftedSphereTopEquiv.{u} n).symm.toLinearMap
    have hval : ∀ x : ℤ, ψ x = x * ψ 1 := by
      intro x
      have hx : x = x • (1 : ℤ) := (mul_one x).symm
      rw [hx, map_zsmul, smul_eq_mul, smul_eq_mul, mul_one]
    have hψ : Function.Surjective ψ := fun y => by
      obtain ⟨x, hx⟩ := hφ y
      exact ⟨(integralLiftedSphereTopEquiv.{u} n) x, by simpa [ψ] using hx⟩
    have hone : ψ 1 = 1 ∨ ψ 1 = -1 := by
      obtain ⟨y, hy⟩ := hψ 1
      rw [hval y, mul_comm] at hy
      exact Int.eq_one_or_neg_one_of_mul_eq_one hy
    have hinj : Function.Injective ψ := by
      intro a b hab
      rw [hval a, hval b] at hab
      rcases hone with h | h
      · rw [h] at hab; simpa using hab
      · rw [h] at hab; simpa using hab
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h2 : ψ ((integralLiftedSphereTopEquiv.{u} n) a) =
          ψ ((integralLiftedSphereTopEquiv.{u} n) b) := by
        simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply]
        exact hab
      exact (integralLiftedSphereTopEquiv.{u} n).injective (hinj h2)
    have hbij : Function.Bijective φ := ⟨hφinj, hφ⟩
    refine ⟨LinearEquiv.ofBijective φ hbij, ?_⟩
    rw [LinearEquiv.ofBijective_apply, hc]

theorem isSphereHomologyGenerator_iff_forall_exists_zsmul (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n c ↔
      ∀ x : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n),
        ∃ k : ℤ, x = k • c := by
  constructor
  · rintro ⟨e, he⟩ x
    refine ⟨e x, ?_⟩
    have h : e ((e x) • c) = e x := by
      rw [map_zsmul, he, smul_eq_mul, mul_one]
    exact (e.injective h).symm
  · intro hdiv
    obtain ⟨k, hk⟩ := hdiv (integralLiftedSphereGenerator.{u} n)
    have hkE : k * ((integralLiftedSphereTopEquiv.{u} n) c) = 1 := by
      have h := congrArg (integralLiftedSphereTopEquiv.{u} n) hk
      rw [map_zsmul, integralLiftedSphereGenerator_coordinate, smul_eq_mul] at h
      exact h.symm
    have hEc : (integralLiftedSphereTopEquiv.{u} n) c = 1 ∨
        (integralLiftedSphereTopEquiv.{u} n) c = -1 := by
      rw [mul_comm] at hkE
      exact Int.eq_one_or_neg_one_of_mul_eq_one hkE
    rcases hEc with h1 | h1
    · exact ⟨integralLiftedSphereTopEquiv n, h1⟩
    · exact ⟨(integralLiftedSphereTopEquiv n).trans (LinearEquiv.neg ℤ), by
        rw [LinearEquiv.trans_apply, h1]
        simp⟩

end DifferentialGeometry.Topology
