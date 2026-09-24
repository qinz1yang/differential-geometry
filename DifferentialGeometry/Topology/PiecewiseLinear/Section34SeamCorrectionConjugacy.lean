import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionFacePreservation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_eq_of_injective_conjugacy
    {A B : Type*} {S T : Set A} {φ : A → B} {ψ : A → A} {H : B → B}
    (hTS : T ⊆ S) (hφ : InjOn φ S) (hψ : MapsTo ψ S S)
    (hconj : ∀ x ∈ S, H (φ x) = φ (ψ x))
    (hH : H '' (φ '' T) = φ '' T) : ψ '' T = T := by
  apply (hφ.image_eq_image_iff (fun _ hx => by
    obtain ⟨x, hx, rfl⟩ := hx
    exact hψ (hTS hx)) hTS).mp
  rw [← image_comp, ← EqOn.image_eq (show EqOn (H ∘ φ) (φ ∘ ψ) T from
    fun x hx => hconj x (hTS hx)), image_comp, hH]

theorem IsPLHomeomorphOn.image_circle_region_of_preserved_bottom_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {R : Set E} {σ : ((Fin 3 → ℝ) × ℝ) × ℝ → E}
    (hσ : IsPLHomeomorphOn σ
      ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) R)
    (hσf : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      σ ((stdTriangleLoop t, u), v) = f ((u, v), t))
    {H : E → E} {ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ}
    (hψ : IsPLHomeomorphOn ψ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hconj : ∀ z ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      H (σ (z, v)) = σ (ψ z, v))
    {K : Set ℝ} (hK : K ⊆ Icc (0 : ℝ) 1)
    (hH : H '' (f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ Icc (0 : ℝ) 1)) =
      f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ Icc (0 : ℝ) 1)) :
    ψ '' (stdSimplexBoundary 2 ×ˢ K) = stdSimplexBoundary 2 ×ˢ K := by
  let κ : (Fin 3 → ℝ) × ℝ → E := fun z => σ (z, 0)
  have hκ : InjOn κ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hσ.bijOn.injOn ⟨hx, by norm_num⟩ ⟨hy, by norm_num⟩ hxy)
  have heq : κ '' (stdSimplexBoundary 2 ×ˢ K) =
      f '' ((K ×ˢ {(0 : ℝ)}) ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := stdTriangleLoop_image.symm.subset hz
      exact ⟨((u, 0), t), ⟨⟨hu, rfl⟩, ht⟩,
        (hσf u (hK hu) 0 (by norm_num) t ht).symm⟩
    · rintro y ⟨⟨⟨u, v⟩, t⟩, ⟨⟨hu, hv⟩, ht⟩, rfl⟩
      change v = 0 at hv
      subst v
      exact ⟨(stdTriangleLoop t, u),
        ⟨stdTriangleLoop_image.subset (mem_image_of_mem stdTriangleLoop ht), hu⟩,
        hσf u (hK hu) 0 (by norm_num) t ht⟩
  apply image_eq_of_injective_conjugacy (prod_mono_right hK) hκ hψ.bijOn.mapsTo
    (fun x hx => hconj x hx 0 (by norm_num))
  rwa [heq]

end DifferentialGeometry.Topology.PiecewiseLinear
