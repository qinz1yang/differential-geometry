import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.TransversePlaneCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLBoundaryCrossingAt.exists_linearEquiv_normalForm {M A B : Set E} {x : E}
    (hx : HasPLBoundaryCrossingAt M A B x) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn h U V ∧ h x = 0 ∧
        ∀ᶠ y in 𝓝 x,
          (y ∈ M ↔ 0 ≤ (L (h y)).1) ∧
            (y ∈ A ↔ (L (h y)).2.2 = 0 ∧ 0 ≤ (L (h y)).1) ∧
              (y ∈ B ↔ (L (h y)).2.1 = 0 ∧ 0 ≤ (L (h y)).1) ∧
                (y ∈ A ∩ B ↔ (L (h y)).2 = 0 ∧ 0 ≤ (L (h y)).1) := by
  obtain ⟨U, V, h, P, Q, ℓ, hU, hV, hxU, hPLh, hhx, hP, hQ, hPQ, hsup, hu, hnear⟩ := hx
  obtain ⟨L, h1, h2, h3, h4⟩ :=
    exists_linearEquiv_of_transverse_planes_of_transverse_functional hP hQ hPQ hsup hu
  have hbranch : ∀ z : E, ((L z).2.2 = 0 ∧ (L z).2.1 = 0) ↔ (L z).2 = 0 := by
    intro z
    rw [← h1 z, ← h2 z, ← Submodule.mem_inf]
    exact h3 z
  refine ⟨U, V, h, L, hU, hV, hxU, hPLh, hhx, ?_⟩
  filter_upwards [hnear] with y hy
  obtain ⟨hM, hA, hB⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hM, h4 (h y)]
  · rw [hA, h1 (h y), h4 (h y)]
  · rw [hB, h2 (h y), h4 (h y)]
  · rw [Set.mem_inter_iff, hA, hB]
    constructor
    · rintro ⟨⟨hPy, hge⟩, hQy, -⟩
      refine ⟨(hbranch (h y)).mp ⟨(h1 (h y)).mp hPy, (h2 (h y)).mp hQy⟩, ?_⟩
      rw [← h4 (h y)]
      exact hge
    · rintro ⟨hz, hge⟩
      obtain ⟨hz2, hz1⟩ := (hbranch (h y)).mpr hz
      have hge' : 0 ≤ ℓ (h y) := by
        rw [h4 (h y)]
        exact hge
      exact ⟨⟨(h1 (h y)).mpr hz2, hge'⟩, (h2 (h y)).mpr hz1, hge'⟩

theorem HasPLCrossingAt.exists_linearEquiv_normalForm {A B : Set E} {x : E}
    (hx : HasPLCrossingAt A B x) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn h U V ∧ h x = 0 ∧
        ((∀ᶠ y in 𝓝 x, (y ∈ A ↔ (L (h y)).2.2 = 0) ∧ (y ∈ B ↔ (L (h y)).2.1 = 0)) ∨
          (∀ᶠ y in 𝓝 x, (y ∈ A ↔ (L (h y)).2.2 = 0) ∧
              (y ∈ B ↔ (L (h y)).2.1 = 0 ∧ 0 ≤ (L (h y)).1)) ∨
            ∀ᶠ y in 𝓝 x, (y ∈ A ↔ (L (h y)).2.2 = 0 ∧ 0 ≤ (L (h y)).1) ∧
              (y ∈ B ↔ (L (h y)).2.1 = 0)) := by
  obtain ⟨U, V, h, P, Q, α, β, hU, hV, hxU, hPLh, hhx, hP, hQ, hPQ, hsup, hα, hβ, hzero, hnear⟩ :=
    hx
  rcases hzero with rfl | rfl
  · rcases hβ with rfl | hβ'
    · obtain ⟨L, h1, h2⟩ := exists_linearEquiv_of_transverse_planes hP hQ hPQ hsup
      refine ⟨U, V, h, L, hU, hV, hxU, hPLh, hhx, Or.inl ?_⟩
      filter_upwards [hnear] with y hy
      obtain ⟨hA, hB⟩ := hy
      simp only [LinearMap.zero_apply, le_refl, and_true] at hA hB
      exact ⟨by rw [hA, h1 (h y)], by rw [hB, h2 (h y)]⟩
    · obtain ⟨L, h1, h2, -, h4⟩ :=
        exists_linearEquiv_of_transverse_planes_of_transverse_functional hP hQ hPQ hsup
          (exists_mem_apply_eq_one_of_exists_mem_apply_ne_zero hβ')
      refine ⟨U, V, h, L, hU, hV, hxU, hPLh, hhx, Or.inr (Or.inl ?_)⟩
      filter_upwards [hnear] with y hy
      obtain ⟨hA, hB⟩ := hy
      simp only [LinearMap.zero_apply, le_refl, and_true] at hA
      exact ⟨by rw [hA, h1 (h y)], by rw [hB, h2 (h y), h4 (h y)]⟩
  · rcases hα with rfl | hα'
    · obtain ⟨L, h1, h2⟩ := exists_linearEquiv_of_transverse_planes hP hQ hPQ hsup
      refine ⟨U, V, h, L, hU, hV, hxU, hPLh, hhx, Or.inl ?_⟩
      filter_upwards [hnear] with y hy
      obtain ⟨hA, hB⟩ := hy
      simp only [LinearMap.zero_apply, le_refl, and_true] at hA hB
      exact ⟨by rw [hA, h1 (h y)], by rw [hB, h2 (h y)]⟩
    · obtain ⟨L, h1, h2, -, h4⟩ :=
        exists_linearEquiv_of_transverse_planes_of_transverse_functional hP hQ hPQ hsup
          (exists_mem_apply_eq_one_of_exists_mem_apply_ne_zero hα')
      refine ⟨U, V, h, L, hU, hV, hxU, hPLh, hhx, Or.inr (Or.inr ?_)⟩
      filter_upwards [hnear] with y hy
      obtain ⟨hA, hB⟩ := hy
      simp only [LinearMap.zero_apply, le_refl, and_true] at hB
      exact ⟨by rw [hA, h1 (h y), h4 (h y)], by rw [hB, h2 (h y)]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
