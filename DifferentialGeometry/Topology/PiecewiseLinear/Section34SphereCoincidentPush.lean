import DifferentialGeometry.Topology.PiecewiseLinear.Section34SphereDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeCoincidentPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_relative_push_of_coincident_disk_of_pseudo_cell
    {S₁ S₂ D T Ω E Eint Ebd : Set (EuclideanSpace ℝ (Fin 3))}
    {p : EuclideanSpace ℝ (Fin 3)} (h₁ : IsPLSphere 2 S₁)
    (hpc : IsPseudoCell E Eint Ebd p) (hD : IsPLBall 2 D)
    (hD₁ : D ⊆ S₁) (hDE : D ⊆ Eint \ {p}) (hE₂ : E ⊆ S₂)
    (hEg : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ S₂)
    (hT : IsClosed T) (hDT : Disjoint D T)
    (htrace : S₁ ∩ S₂ ⊆ D ∪ T) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧ EqOn Φ id T ∧
      Φ '' S₁ ⊆ S₁ ∪ Ω ∧ Φ '' S₁ ∩ S₂ = (S₁ \ D) ∩ S₂ := by
  obtain ⟨Γ, r, -, hr, hΓ₁, hDΓ, -, -, hΓg⟩ := h₁.exists_disk_chart_around_disk hD hD₁
  let W := (Ω ∩ {x | ∀ᶠ y in 𝓝 x, y ∈ Γ ↔ y ∈ S₁}) ∩
    {x | ∀ᶠ y in 𝓝 x, y ∈ E ↔ y ∈ S₂}
  have hW : IsOpen W := (hΩ.inter isOpen_setOfPred_eventually_nhds).inter
    isOpen_setOfPred_eventually_nhds
  have hDW : D ⊆ W := fun x hx => ⟨⟨hDΩ hx, hΓg x hx⟩, hEg x hx⟩
  have hWΩ : W ⊆ Ω := fun _ hx => hx.1.1
  have hΓE : Γ ∩ E ⊆ D ∪ T := fun _ hx => htrace ⟨hΓ₁ hx.1, hE₂ hx.2⟩
  obtain ⟨Φ, hΦ, hfix, hfixT, -, -, hlocal⟩ :=
    hpc.exists_relative_push_of_coincident_patch_neighborhood hr hD hDΓ hDE hT hDT
      hΓE hW hDW
  have hmap : MapsTo Φ W W := by
    intro y hy
    by_contra hn
    have hyy := hΦ.bijOn.injOn (mem_univ y) (mem_univ (Φ y)) (hfix hn).symm
    exact hn (hyy ▸ hy)
  refine ⟨Φ, hΦ, hfix.mono (compl_subset_compl.mpr hWΩ), hfixT, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxW : x ∈ W
    · exact Or.inr (hWΩ (hmap hxW))
    · rw [hfix hxW]
      exact Or.inl hx
  · ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hy₂⟩
      by_cases hyW : y ∈ W
      · have hyΓ := hyW.1.2.self_of_nhds.mpr hy
        have hΦyW := hmap hyW
        have hyE := hΦyW.2.self_of_nhds.mpr hy₂
        have hrem := hlocal.subset ⟨⟨y, hyΓ, rfl⟩, hyE⟩
        exact ⟨⟨hΓ₁ hrem.1.1, hrem.1.2⟩, hy₂⟩
      · rw [hfix hyW] at hy₂ ⊢
        exact ⟨⟨hy, fun hyD => hyW (hDW hyD)⟩, hy₂⟩
    · rintro ⟨⟨hx₁, hxD⟩, hx₂⟩
      by_cases hxW : x ∈ W
      · have hxΓ := hxW.1.2.self_of_nhds.mpr hx₁
        have hxE := hxW.2.self_of_nhds.mpr hx₂
        obtain ⟨⟨y, hyΓ, hyx⟩, -⟩ := hlocal.superset ⟨⟨hxΓ, hxD⟩, hxE⟩
        exact ⟨⟨y, hΓ₁ hyΓ, hyx⟩, hx₂⟩
      · exact ⟨⟨x, hx₁, hfix hxW⟩, hx₂⟩

theorem IsPLSphere.exists_relative_push_of_coincident_disk
    {S₁ S₂ D T Ω : Set (EuclideanSpace ℝ (Fin 3))}
    (h₁ : IsPLSphere 2 S₁) (h₂ : IsPLSphere 2 S₂) (hD : IsPLBall 2 D)
    (hD₁ : D ⊆ S₁) (hD₂ : D ⊆ S₂) (hT : IsClosed T) (hDT : Disjoint D T)
    (htrace : S₁ ∩ S₂ ⊆ D ∪ T) (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id Ωᶜ ∧ EqOn Φ id T ∧
      Φ '' S₁ ⊆ S₁ ∪ Ω ∧ Φ '' S₁ ∩ S₂ = (S₁ \ D) ∩ S₂ := by
  obtain ⟨E, s, p, hs, hE₂, hDE, hpE, hpD, hEg⟩ :=
    h₂.exists_disk_chart_around_disk hD hD₂
  have hpc := hs.isPseudoCell_of_mem_interior hpE
  have hDE' : D ⊆ (E \ s '' stdSimplexBoundary 2) \ {p} := by
    intro x hx
    exact ⟨hs.image_openSimplex_stdVertices ▸ hDE hx, fun hxp => hpD (hxp ▸ hx)⟩
  exact h₁.exists_relative_push_of_coincident_disk_of_pseudo_cell hpc hD hD₁ hDE' hE₂ hEg
    hT hDT htrace hΩ hDΩ

end DifferentialGeometry.Topology.PiecewiseLinear
