import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFillingClosedBall
import DifferentialGeometry.Topology.ThreeManifold.schoenflies
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesCore
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesRoundSphere
import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenfliesTwoSided

set_option autoImplicit false

open Function Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

private noncomputable def jordanSides (e : S² → ℝ³)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    SphereSeparation.SmoothSphereSides (Set.range e) :=
  SphereSeparation.jordanBrouwer_openThreeSpace e he (Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞)

private theorem image_sphere_eq_range_of_image_ball_eq_compactSide (e : S² → ℝ³)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (Φ : ℝ³ ≃ₘ[ℝ] ℝ³)
    (hball : Φ '' ball (0 : ℝ³) 1 = (jordanSides e he).compactSide) :
    Φ '' S² = Set.range e :=
  calc Φ '' S² = Φ '' frontier (ball (0 : ℝ³) 1) := by rw [frontier_ball 0 one_ne_zero]
    _ = frontier (Φ '' ball (0 : ℝ³) 1) := by
        simpa only [Diffeomorph.coe_toHomeomorph] using
          Φ.toHomeomorph.image_frontier (ball (0 : ℝ³) 1)
    _ = frontier (jordanSides e he).compactSide := by rw [hball]
    _ = Set.range e :=
        SphereSeparation.SphereSides.frontier_compactSide (jordanSides e he).toSphereSides

theorem exists_ambient_diffeomorph_sphere_ball_endSide_of_smoothSchoenfliesThree
    (h : SphereSeparation.smoothSchoenfliesThree) (e : S² → ℝ³)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
      Φ '' S² = Set.range e ∧
        Φ '' ball (0 : ℝ³) 1 = (jordanSides e he).compactSide ∧
        Φ '' (closedBall (0 : ℝ³) 1)ᶜ = (jordanSides e he).endSide := by
  obtain ⟨Φ, hball, hend⟩ :=
    smoothSchoenfliesThree_iff_smoothSchoenfliesTwoSided.mp h e he
  exact ⟨Φ, image_sphere_eq_range_of_image_ball_eq_compactSide e he Φ hball, hball, hend⟩

theorem smoothSchoenfliesThree_iff_exists_ambient_diffeomorph_sphere_ball_endSide :
    SphereSeparation.smoothSchoenfliesThree ↔
      ∀ (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
        ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
          Φ '' S² = Set.range e ∧
            Φ '' ball (0 : ℝ³) 1 = (jordanSides e he).compactSide ∧
            Φ '' (closedBall (0 : ℝ³) 1)ᶜ = (jordanSides e he).endSide := by
  constructor
  · intro h e he
    exact exists_ambient_diffeomorph_sphere_ball_endSide_of_smoothSchoenfliesThree h e he
  · intro h
    refine SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr ?_
    intro e he
    obtain ⟨Φ, hΦ, -, -⟩ := h e he
    exact ⟨Φ, hΦ⟩

theorem smoothSchoenfliesThree_iff_exists_ambient_diffeomorph_any_of_three :
    SphereSeparation.smoothSchoenfliesThree ↔
      ((∀ (e : S² → ℝ³), Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
          ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e) ∨
        (∀ (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
          ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' ball (0 : ℝ³) 1 = (jordanSides e he).compactSide) ∨
        (∀ (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e),
          ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
            Φ '' (closedBall (0 : ℝ³) 1)ᶜ = (jordanSides e he).endSide)) := by
  constructor
  · intro h
    exact Or.inl (SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mp h)
  · rintro (h | h | h)
    · exact SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr h
    · exact SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mpr
        (fun e he => h e he)
    · exact SphereSeparation.smoothSchoenfliesThree_iff_closedBallComplement_endSide.mpr
        (fun e he => h e he)

theorem smoothSchoenfliesThree_iff_ballFilling_and_twoSided_and_core :
    SphereSeparation.smoothSchoenfliesThree ↔
      (SphereSeparation.smoothSchoenfliesBallFilling ∧ smoothSchoenfliesTwoSided ∧
        smoothSchoenfliesCore) := by
  constructor
  · intro h
    exact ⟨SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp h,
      smoothSchoenfliesThree_iff_smoothSchoenfliesTwoSided.mp h,
      smoothSchoenfliesCore_iff_smoothSchoenfliesBallFilling.mpr
        (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp h)⟩
  · rintro ⟨-, ht, -⟩
    exact smoothSchoenfliesThree_iff_smoothSchoenfliesTwoSided.mpr ht

theorem exists_ambient_diffeomorph_sphere_ball_endSide_roundSphere :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³,
      Φ '' S² = Set.range (Subtype.val : S² → ℝ³) ∧
        Φ '' ball (0 : ℝ³) 1 =
          (jordanSides (Subtype.val : S² → ℝ³)
            isSmoothEmbedding_sphereTwo_subtype).compactSide ∧
        Φ '' (closedBall (0 : ℝ³) 1)ᶜ =
          (jordanSides (Subtype.val : S² → ℝ³)
            isSmoothEmbedding_sphereTwo_subtype).endSide := by
  obtain ⟨Φ, hball, hend⟩ := exists_ambient_diffeomorph_twoSides_roundSphere
  exact ⟨Φ, image_sphere_eq_range_of_image_ball_eq_compactSide _ _ Φ hball, hball, hend⟩

theorem exists_ambient_diffeomorph_image_sphere_of_surjective_comp (e : S² → ℝ³)
    (φ : S² → S²) (hφ : Surjective φ) :
    (∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e) →
      ∃ Ψ : ℝ³ ≃ₘ[ℝ] ℝ³, Ψ '' S² = Set.range (e ∘ φ) := by
  rintro ⟨Φ, hΦ⟩
  exact ⟨Φ, by rw [Set.range_comp, hφ.range_eq, Set.image_univ, hΦ]⟩

end DifferentialGeometry.Topology.ThreeManifold
