import DifferentialGeometry.Geometry.MinimalSurface.Width.Metric








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M] {n : ℕ}



theorem regularFamilyMaximum_scale (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (c : ℝ) (hc : 0 < c)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top))) :
    regularFamilyMaximum (scaleMetric c hc g) e (he.of_le (by exact_mod_cast le_top)) Γ =
      c * regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ := by
  obtain ⟨k, hk⟩ := regularFamilyMaximum_attained (scaleMetric c hc g) e he hemb hi Γ
  obtain ⟨j, hj⟩ := regularFamilyMaximum_attained g e he hemb hi Γ
  have hu := mul_le_mul_of_nonneg_left (regularLeastArea_le_familyMaximum g e he hemb hi Γ k) hc.le
  have hl := regularLeastArea_le_familyMaximum (scaleMetric c hc g) e he hemb hi Γ j
  rw [regularLeastArea_scale] at hk hl
  rw [hj] at hl
  exact le_antisymm (hk ▸ hu) hl



theorem exists_initial_regularFamily_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    ∃ Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)),
      Γ ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ ∧
      0 ≤ classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ ∧
      classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
        regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ ∧
      ∀ (c : ℝ) (hc : 0 < c),
        regularFamilyMaximum (scaleMetric c hc g) e (he.of_le (by exact_mod_cast le_top)) Γ =
          c * regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ ∧
        classWidth (scaleMetric c hc g) e (he.of_le (by exact_mod_cast le_top)) hemb ξ ≤
          c * regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) Γ := by
  obtain ⟨Γ, hΓ⟩ := regularFamilyRepresentatives_nonempty g e he hemb ξ
  refine ⟨Γ, hΓ, classWidth_nonneg g e he hemb hi ξ,
    classWidth_le_familyMaximum g e he hemb hi ξ hΓ, fun c hc => ?_⟩
  have heq := regularFamilyMaximum_scale g c hc e he hemb hi Γ
  exact ⟨heq, (classWidth_le_familyMaximum (scaleMetric c hc g) e he hemb hi ξ hΓ).trans_eq heq⟩

end DifferentialGeometry.Geometry
