import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import DifferentialGeometry.Topology.SphereSeparation.Schoenflies
import DifferentialGeometry.Topology.SphereSeparation.SchoenfliesSides
import DifferentialGeometry.Topology.Embedding.Sphere

set_option autoImplicit false

open Function Set Metric Manifold
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.SphereSeparation

local notation "E³" => EuclideanThree
local notation "S²" => sphere (0 : E³) 1

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

private theorem isSmoothEmbedding_coe_sphereThree :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x : S² => (x : E³)) :=
  isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

noncomputable def smoothSchoenfliesBallFilling : Prop :=
  ∀ (e : S² → E³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' ball (0 : E³) 1 =
        (jordanBrouwer_openThreeSpace e he (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide

theorem smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling :
    smoothSchoenfliesThree ↔ smoothSchoenfliesBallFilling := by
  constructor
  · intro hSch e he
    obtain ⟨D, d, hsphere, hd, hcl⟩ :=
      exists_ball_sphereSides_of_smoothSchoenflies hSch e he
    exact ⟨D, by rw [← hd, SphereSides.unique d _]⟩
  · intro hball e he
    obtain ⟨D, hD⟩ := hball e he
    refine ⟨D.toPartialDiffeomorph, subset_univ _, ?_⟩
    change (D : E³ → E³) '' S² = range e
    calc (D : E³ → E³) '' S²
        = (D : E³ → E³) '' frontier (ball (0 : E³) 1) := by
          rw [frontier_ball 0 one_ne_zero]
      _ = frontier ((D : E³ → E³) '' ball (0 : E³) 1) :=
          Homeomorph.image_frontier D.toHomeomorph _
      _ = frontier (jordanBrouwer_openThreeSpace e he
            (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by rw [hD]
      _ = range e := SphereSides.frontier_compactSide _

theorem smoothSchoenfliesThree_iff_exists_ambient_diffeomorph :
    smoothSchoenfliesThree ↔
      ∀ (e : S² → E³), IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
        ∃ Φ : E³ ≃ₘ[ℝ] E³, Φ '' S² = range e := by
  constructor
  · intro hSch e he
    exact exists_global_diffeomorph_of_smoothSchoenflies hSch e he
  · intro h e he
    obtain ⟨Φ, hΦ⟩ := h e he
    refine ⟨Φ.toPartialDiffeomorph, subset_univ _, ?_⟩
    change (Φ : E³ → E³) '' S² = range e
    rw [hΦ]

theorem exists_diffeomorph_image_sphere_of_diffeomorph_comp_coe (Φ : E³ ≃ₘ[ℝ] E³) :
    ∃ Ψ : E³ ≃ₘ[ℝ] E³, Ψ '' S² = range (Φ ∘ (Subtype.val : S² → E³)) := by
  refine ⟨Φ, ?_⟩
  rw [range_comp, Subtype.range_coe]

theorem exists_diffeomorph_image_ball_of_diffeomorph_comp_coe (Φ : E³ ≃ₘ[ℝ] E³) :
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' ball (0 : E³) 1 =
        (jordanBrouwer_openThreeSpace (Φ ∘ (Subtype.val : S² → E³))
          (isSmoothEmbedding_coe_sphereThree.postcomp_diffeomorph Φ)
          (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by
  let d₀ := standardUnitSphereSides.image Φ.toHomeomorph
  have hidx : range (Φ ∘ (Subtype.val : S² → E³)) = Φ '' S² := by
    rw [range_comp, Subtype.range_coe]
  have hB : d₀.compactSide = Φ '' ball (0 : E³) 1 := by
    change (standardUnitSphereSides.image Φ.toHomeomorph).compactSide = Φ '' ball (0 : E³) 1
    rw [SphereSides.image_compactSide, Diffeomorph.coe_toHomeomorph]
    rfl
  refine ⟨Φ, ?_⟩
  rw [← hB]
  exact (SphereSides.side_sets_unique_of_core_properties
    (jordanBrouwer_openThreeSpace (Φ ∘ (Subtype.val : S² → E³))
      (isSmoothEmbedding_coe_sphereThree.postcomp_diffeomorph Φ)
      (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).toSphereSides
    d₀.compactSide d₀.endSide d₀.isOpen_compactSide d₀.isOpen_endSide
    d₀.isConnected_compactSide d₀.isConnected_endSide d₀.disjoint
    (by rw [hidx]; simpa only [Diffeomorph.coe_toHomeomorph] using d₀.union_eq_compl)
    d₀.isCompact_closure_compactSide
    d₀.not_isCompact_closure_endSide).1

end DifferentialGeometry.Topology.SphereSeparation
