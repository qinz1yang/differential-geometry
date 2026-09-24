import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFillingClosedBall
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesRoundSphere

open scoped ContDiff Manifold
open Set Metric

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

theorem smoothSchoenfliesBallFilling_iff_exists_ambient_diffeomorph :
    SphereSeparation.smoothSchoenfliesBallFilling ↔
      ∀ (e : S² → ℝ³), Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
        ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e :=
  (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling).symm.trans
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph

theorem compactSide_jordanBrouwer_openThreeSpace_coe_sphere :
    (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
      isSmoothEmbedding_sphereTwo_subtype
      (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide = ball (0 : ℝ³) 1 :=
  (SphereSeparation.SphereSides.side_sets_unique_of_core_properties
    (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
      isSmoothEmbedding_sphereTwo_subtype
      (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).toSphereSides
    (ball (0 : ℝ³) 1) ((closedBall (0 : ℝ³) 1)ᶜ)
    SphereSeparation.standardUnitSphereSides.isOpen_compactSide
    SphereSeparation.standardUnitSphereSides.isOpen_endSide
    SphereSeparation.standardUnitSphereSides.isConnected_compactSide
    SphereSeparation.standardUnitSphereSides.isConnected_endSide
    SphereSeparation.standardUnitSphereSides.disjoint
    (by rw [Subtype.range_coe]
        exact SphereSeparation.standardUnitSphereSides.union_eq_compl)
    SphereSeparation.standardUnitSphereSides.isCompact_closure_compactSide
    SphereSeparation.standardUnitSphereSides.not_isCompact_closure_endSide).1.symm

theorem exists_diffeomorph_image_ball_roundSphere :
    ∃ D : ℝ³ ≃ₘ[ℝ] ℝ³,
      D '' ball (0 : ℝ³) 1 =
        (SphereSeparation.jordanBrouwer_openThreeSpace (Subtype.val : S² → ℝ³)
          isSmoothEmbedding_sphereTwo_subtype
          (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)).compactSide := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞, ?_⟩
  rw [Diffeomorph.coe_refl, Set.image_id, compactSide_jordanBrouwer_openThreeSpace_coe_sphere]

end DifferentialGeometry.Topology.ThreeManifold
