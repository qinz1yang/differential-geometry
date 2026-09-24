import DifferentialGeometry.Topology.Homology.SphereGenerator

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable (n : ℕ) (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))

theorem isSphereHomologyGenerator_iff_exists_functional :
    IsSphereHomologyGenerator n c ↔
      ∃ φ : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ,
        φ c = 1 := by
  refine (isSphereHomologyGenerator_iff_exists_surjective_functional n c).trans ⟨?_, ?_⟩
  · rintro ⟨φ, -, hφ⟩
    exact ⟨φ, hφ⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun y => ⟨y • c, by rw [map_zsmul, hφ, smul_eq_mul, mul_one]⟩, hφ⟩

theorem isSphereHomologyGenerator_iff_exists_isUnit :
    IsSphereHomologyGenerator n c ↔
      ∃ φ : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ,
        IsUnit (φ c) := by
  refine (isSphereHomologyGenerator_iff_exists_functional n c).trans ⟨?_, ?_⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, by rw [hφ]; exact isUnit_one⟩
  · rintro ⟨φ, hφ⟩
    rcases Int.isUnit_iff.mp hφ with h | h
    · exact ⟨φ, h⟩
    · exact ⟨-φ, by rw [LinearMap.neg_apply, h, neg_neg]⟩

theorem isSphereHomologyGenerator_iff_bijective_zsmul :
    IsSphereHomologyGenerator n c ↔ Function.Bijective (fun z : ℤ => z • c) := by
  constructor
  · intro hc
    obtain ⟨e, he⟩ := hc
    refine ⟨fun a b hab => ?_, fun x => ⟨e x, ?_⟩⟩
    · have h := congrArg e hab
      rw [map_zsmul, map_zsmul, he] at h
      simpa using h
    · apply e.injective
      rw [map_zsmul, he]
      simp
  · intro h
    refine (isSphereHomologyGenerator_iff_forall_exists_zsmul n c).mpr fun x => ?_
    obtain ⟨k, hk⟩ := h.2 x
    exact ⟨k, hk.symm⟩

theorem isSphereHomologyGenerator_iff_forall_isUnit_of_exists_eq_zsmul :
    IsSphereHomologyGenerator n c ↔
      ∀ k : ℤ, (∃ d : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n),
        c = k • d) → IsUnit k := by
  constructor
  · intro hc k hd
    obtain ⟨e, he⟩ := hc
    obtain ⟨d, hd⟩ := hd
    have h1 : k • e d = 1 := by rw [← map_zsmul, ← hd, he]
    exact Int.isUnit_iff.mpr
      (Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [smul_eq_mul] using h1))
  · intro h
    have hc : c = (integralLiftedSphereTopEquiv n c) • integralLiftedSphereGenerator.{u} n := by
      calc c = (integralLiftedSphereTopEquiv n).symm (integralLiftedSphereTopEquiv n c) :=
            ((integralLiftedSphereTopEquiv n).symm_apply_apply c).symm
        _ = (integralLiftedSphereTopEquiv n).symm
              ((integralLiftedSphereTopEquiv n c) • (1 : ℤ)) := by
            rw [smul_eq_mul, mul_one]
        _ = (integralLiftedSphereTopEquiv n c) •
              (integralLiftedSphereTopEquiv n).symm 1 := map_zsmul _ _ _
        _ = (integralLiftedSphereTopEquiv n c) • integralLiftedSphereGenerator.{u} n := rfl
    have hk := h (integralLiftedSphereTopEquiv n c)
      ⟨integralLiftedSphereGenerator.{u} n, hc⟩
    exact (isSphereHomologyGenerator_iff_exists_isUnit n c).mpr
      ⟨integralLiftedSphereTopEquiv n, hk⟩

end DifferentialGeometry.Topology
