import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.ThreeManifold.schoenflies

open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "E³" => EuclideanSpace ℝ (Fin 3)

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

theorem compactSide_congr_of_range_eq {e₁ e₂ : SphereTwo → E³}
    (he₁ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₂) (h : range e₁ = range e₂) :
    (SphereSeparation.jordanBrouwer_openThreeSpace e₁ he₁
        (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide =
      (SphereSeparation.jordanBrouwer_openThreeSpace e₂ he₂
        (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by
  let d₁ := SphereSeparation.jordanBrouwer_openThreeSpace e₁ he₁
    (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)
  let d₂ := SphereSeparation.jordanBrouwer_openThreeSpace e₂ he₂
    (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)
  have hunion : d₂.compactSide ∪ d₂.endSide = (range e₁)ᶜ := by
    rw [d₂.union_eq_compl, h]
  exact ((d₁.side_sets_unique_of_core_properties d₂.compactSide d₂.endSide
    d₂.isOpen_compactSide d₂.isOpen_endSide d₂.isConnected_compactSide d₂.isConnected_endSide
    d₂.disjoint hunion d₂.isCompact_closure_compactSide
    d₂.not_isCompact_closure_endSide).1).symm

theorem exists_diffeomorph_image_ball_of_range_eq_sphere {e : SphereTwo → E³}
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) {c : E³} {r : ℝ} (hr : 0 < r)
    (hrange : range e = Metric.sphere c r) :
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' Metric.ball 0 1 =
        (SphereSeparation.jordanBrouwer_openThreeSpace e he
          (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_image_sphere c hr
  have heΦ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (Φ ∘ (Subtype.val : SphereTwo → E³)) :=
    (isSmoothEmbedding_coe_sphere (E := E³) (n := 2)).postcomp_diffeomorph Φ
  obtain ⟨D, hD⟩ := SphereSeparation.exists_diffeomorph_image_ball_of_diffeomorph_comp_coe Φ
  refine ⟨D, ?_⟩
  have hrange' : range (Φ ∘ (Subtype.val : SphereTwo → E³)) = range e := by
    rw [range_comp, Subtype.range_coe, hΦ, hrange]
  rw [hD, compactSide_congr_of_range_eq heΦ he hrange']

end DifferentialGeometry.Topology.ThreeManifold
