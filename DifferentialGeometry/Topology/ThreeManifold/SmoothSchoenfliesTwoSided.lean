import DifferentialGeometry.Topology.SphereSeparation.CompactSide
import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFillingClosedBall
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesBallFillingFrontier
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesRoundSphere

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Metric

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

noncomputable def smoothSchoenfliesTwoSided : Prop :=
  ∀ (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
      Φ '' ball (0 : ℝ³) 1 =
          (SphereSeparation.jordanBrouwer_openThreeSpace e he
            (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide ∧
        Φ '' (closedBall (0 : ℝ³) 1)ᶜ =
          (SphereSeparation.jordanBrouwer_openThreeSpace e he
            (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).endSide

theorem smoothSchoenfliesThree_iff_smoothSchoenfliesTwoSided :
    SphereSeparation.smoothSchoenfliesThree ↔ smoothSchoenfliesTwoSided := by
  constructor
  · intro h e he
    obtain ⟨D, hD⟩ :=
      (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp h) e he
    refine ⟨D, hD, ?_⟩
    have hcl : D '' closedBall (0 : ℝ³) 1 = closure (D '' ball (0 : ℝ³) 1) := by
      change D.toHomeomorph '' closedBall (0 : ℝ³) 1 =
        closure (D.toHomeomorph '' ball (0 : ℝ³) 1)
      rw [← D.toHomeomorph.image_closure, closure_ball (0 : ℝ³) one_ne_zero]
    rw [show D '' (closedBall (0 : ℝ³) 1)ᶜ = (D '' closedBall (0 : ℝ³) 1)ᶜ from
        (by simpa only [Diffeomorph.coe_toHomeomorph] using
          D.toHomeomorph.image_compl (closedBall (0 : ℝ³) 1)),
      hcl, hD,
      SphereSeparation.SphereSides.endSide_eq_compl_closure_compactSide
        (SphereSeparation.jordanBrouwer_openThreeSpace e he
          (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).toSphereSides]
  · intro h
    refine SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mpr ?_
    intro e he
    obtain ⟨D, hD, -⟩ := h e he
    exact ⟨D, hD⟩

theorem exists_ambient_diffeomorph_twoSides_roundSphere :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
      Φ '' ball (0 : ℝ³) 1 =
          (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
            isSmoothEmbedding_sphereTwo_subtype
            (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide ∧
        Φ '' (closedBall (0 : ℝ³) 1)ᶜ =
          (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
            isSmoothEmbedding_sphereTwo_subtype
            (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).endSide := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞, ?_, ?_⟩
  · rw [Diffeomorph.coe_refl, Set.image_id]
    exact compactSide_jordanBrouwer_openThreeSpace_coe_sphere.symm
  · rw [Diffeomorph.coe_refl, Set.image_id,
      SphereSeparation.SphereSides.endSide_eq_compl_closure_compactSide
        (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
          isSmoothEmbedding_sphereTwo_subtype
          (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).toSphereSides,
      compactSide_jordanBrouwer_openThreeSpace_coe_sphere, closure_ball (0 : ℝ³) one_ne_zero]

end DifferentialGeometry.Topology.ThreeManifold
