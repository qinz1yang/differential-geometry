import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems

set_option autoImplicit false

open Function Set Metric Manifold
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.SphereSeparation

local notation "E³" => EuclideanThree
local notation "S²" => sphere (0 : E³) 1

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

private theorem isSmoothEmbedding_coe_sphereThree_local :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun x : S² => (x : E³)) :=
  isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

theorem smoothSchoenfliesBallFilling_iff_closedBall_closure :
    smoothSchoenfliesBallFilling ↔
      ∀ (e : S² → E³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
        ∃ D : E³ ≃ₘ[ℝ] E³,
          D '' closedBall (0 : E³) 1 =
            closure (jordanBrouwer_openThreeSpace e he
              (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).compactSide := by
  constructor
  · intro h e he
    obtain ⟨D, hD⟩ := h e he
    refine ⟨D, ?_⟩
    rw [← closure_ball (0 : E³) one_ne_zero, ← hD]
    simpa only [Diffeomorph.coe_toHomeomorph] using D.toHomeomorph.image_closure (ball (0 : E³) 1)
  · intro h e he
    obtain ⟨D, hD⟩ := h e he
    refine ⟨D, ?_⟩
    rw [← SphereSides.interior_closure_compactSide, ← hD,
      ← interior_closedBall (0 : E³) one_ne_zero]
    simpa only [Diffeomorph.coe_toHomeomorph] using
      D.toHomeomorph.image_interior (closedBall (0 : E³) 1)

private theorem compl_closure_compactSide_eq_endSide
    {N : Type*} [TopologicalSpace N] {S : Set N} (d : SphereSides S) :
    (closure d.compactSide)ᶜ = d.endSide := by
  rw [d.closure_compactSide]
  ext x
  constructor
  · intro hx
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
    have hmem : x ∈ d.compactSide ∪ d.endSide := by
      rw [d.union_eq_compl]
      exact hx.2
    rcases hmem with h | h
    · exact absurd h hx.1
    · exact h
  · intro hx
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨fun hB => Set.disjoint_left.mp d.disjoint hB hx,
      fun hS => d.endSide_subset_compl hx hS⟩

private theorem image_closedBall_compl (D : E³ ≃ₘ[ℝ] E³) :
    D '' (closedBall (0 : E³) 1)ᶜ = (D '' closedBall (0 : E³) 1)ᶜ := by
  simpa only [Diffeomorph.coe_toHomeomorph] using
    D.toHomeomorph.image_compl (closedBall (0 : E³) 1)

theorem smoothSchoenfliesBallFilling_iff_closedBallComplement_endSide :
    smoothSchoenfliesBallFilling ↔
      ∀ (e : S² → E³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
        ∃ D : E³ ≃ₘ[ℝ] E³,
          D '' (closedBall (0 : E³) 1)ᶜ =
            (jordanBrouwer_openThreeSpace e he
              (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).endSide := by
  rw [smoothSchoenfliesBallFilling_iff_closedBall_closure]
  constructor
  · intro h e he
    obtain ⟨D, hD⟩ := h e he
    refine ⟨D, ?_⟩
    rw [image_closedBall_compl, hD, compl_closure_compactSide_eq_endSide]
  · intro h e he
    obtain ⟨D, hD⟩ := h e he
    refine ⟨D, ?_⟩
    rw [← compl_compl (D '' closedBall (0 : E³) 1), ← image_closedBall_compl D, hD,
      ← compl_closure_compactSide_eq_endSide, compl_compl]

theorem smoothSchoenfliesThree_iff_closedBallComplement_endSide :
    smoothSchoenfliesThree ↔
      ∀ (e : S² → E³) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
        ∃ D : E³ ≃ₘ[ℝ] E³,
          D '' (closedBall (0 : E³) 1)ᶜ =
            (jordanBrouwer_openThreeSpace e he
              (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).endSide :=
  smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.trans
    smoothSchoenfliesBallFilling_iff_closedBallComplement_endSide

private theorem endSide_jordanBrouwer_coe_sphere :
    (jordanBrouwer_openThreeSpace (Subtype.val : S² → E³)
      isSmoothEmbedding_coe_sphereThree_local
      (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).endSide = (closedBall (0 : E³) 1)ᶜ := by
  have hrange : Set.range (Subtype.val : S² → E³) = Metric.sphere (0 : E³) 1 := by
    rw [Subtype.range_coe]
  exact (SphereSides.side_sets_unique_of_core_properties
    (jordanBrouwer_openThreeSpace (Subtype.val : S² → E³)
      isSmoothEmbedding_coe_sphereThree_local
      (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).toSphereSides
    (ball (0 : E³) 1) ((closedBall (0 : E³) 1)ᶜ)
    standardUnitSphereSides.isOpen_compactSide
    standardUnitSphereSides.isOpen_endSide
    standardUnitSphereSides.isConnected_compactSide
    standardUnitSphereSides.isConnected_endSide
    standardUnitSphereSides.disjoint
    (by rw [hrange]; exact standardUnitSphereSides.union_eq_compl)
    standardUnitSphereSides.isCompact_closure_compactSide
    standardUnitSphereSides.not_isCompact_closure_endSide).2.symm

theorem exists_diffeomorph_image_closedBallComplement_roundSphere :
    ∃ D : E³ ≃ₘ[ℝ] E³,
      D '' (closedBall (0 : E³) 1)ᶜ =
        (jordanBrouwer_openThreeSpace (Subtype.val : S² → E³)
          isSmoothEmbedding_coe_sphereThree_local
          (Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞)).endSide := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, E³) E³ ∞, ?_⟩
  rw [Diffeomorph.coe_refl, Set.image_id, endSide_jordanBrouwer_coe_sphere]

end DifferentialGeometry.Topology.SphereSeparation
