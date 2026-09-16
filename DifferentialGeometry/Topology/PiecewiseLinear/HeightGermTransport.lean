import DifferentialGeometry.Topology.PiecewiseLinear.ParametricTriangleHeightCut

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_image_mem_le_of_height_preserving_homeomorph
    {E : Type*} [TopologicalSpace E] {Q : Set E} (H : E ≃ₜ E)
    (ℓ : E → ℝ) (hheight : ∀ x, ℓ (H x) = ℓ x) {q : E}
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ x ≤ ℓ q) :
    ∀ᶠ y in 𝓝 (H q), y ∈ H '' Q → ℓ y ≤ ℓ (H q) := by
  have ht : Tendsto H.symm (𝓝 (H q)) (𝓝 q) := by
    simpa only [H.symm_apply_apply] using
      (H.symm.continuous.continuousAt (x := H q)).tendsto
  filter_upwards [ht.eventually hhalf] with y hy
  rintro ⟨x, hx, rfl⟩
  simp only [H.symm_apply_apply] at hy
  simpa only [hheight] using hy hx

theorem eventually_image_mem_ge_of_height_preserving_homeomorph
    {E : Type*} [TopologicalSpace E] {Q : Set E} (H : E ≃ₜ E)
    (ℓ : E → ℝ) (hheight : ∀ x, ℓ (H x) = ℓ x) {q : E}
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ q ≤ ℓ x) :
    ∀ᶠ y in 𝓝 (H q), y ∈ H '' Q → ℓ (H q) ≤ ℓ y := by
  have ht : Tendsto H.symm (𝓝 (H q)) (𝓝 q) := by
    simpa only [H.symm_apply_apply] using
      (H.symm.continuous.continuousAt (x := H q)).tendsto
  filter_upwards [ht.eventually hhalf] with y hy
  rintro ⟨x, hx, rfl⟩
  simp only [H.symm_apply_apply] at hy
  simpa only [hheight] using hy hx

theorem eventually_image_boundary_fiber_iff_of_height_preserving_homeomorph
    {E : Type*} [TopologicalSpace E] {Q J : Set E} (H : E ≃ₜ E)
    (ℓ : E → ℝ) (hheight : ∀ x, ℓ (H x) = ℓ x) {q : E}
    (hboundary : ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ ℓ x = ℓ q) :
    ∀ᶠ y in 𝓝 (H q), y ∈ H '' J ↔ y ∈ H '' Q ∧ ℓ y = ℓ (H q) := by
  have ht : Tendsto H.symm (𝓝 (H q)) (𝓝 q) := by
    simpa only [H.symm_apply_apply] using
      (H.symm.continuous.continuousAt (x := H q)).tendsto
  filter_upwards [ht.eventually hboundary] with y hy
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [H.symm_apply_apply] at hy
    have hx' : x ∈ Q ∧ ℓ x = ℓ q := by
      exact hy.mp hx
    exact ⟨⟨x, hx'.1, rfl⟩, by simpa only [hheight] using hx'.2⟩
  · rintro ⟨⟨x, hx, rfl⟩, heq⟩
    simp only [H.symm_apply_apply] at hy
    refine ⟨x, ?_, rfl⟩
    apply hy.mpr
    simpa only [hheight] using And.intro hx heq

end DifferentialGeometry.Topology.PiecewiseLinear
