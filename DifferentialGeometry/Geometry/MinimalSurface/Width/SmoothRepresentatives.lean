import DifferentialGeometry.Geometry.MinimalSurface.Width.Class
import DifferentialGeometry.Geometry.Measure.Area.SmoothFamilyApproximation



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]
  {n : ℕ}



theorem exists_smoothFamily_maximum_lt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)))
      (hs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => (S k).val.val (t : loopCircle))),
      S ∈ regularFamilyRepresentatives e (he.of_le (by exact_mod_cast le_top)) hemb ξ ∧
      regularFamilyMaximum g e (he.of_le (by exact_mod_cast le_top)) S <
        classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ + ε ∧
      (∀ (d : ℕ) (a : M → EuclideanSpace ℝ (Fin d))
        (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ a) (j : ℕ),
        Continuous[inferInstance, finiteRegularLoopTopology a ha j]
          (fun k => (⟨(S k).val.val, (hs k).of_le (by exact_mod_cast le_top)⟩ :
            finiteRegularLoop j E M))) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨Γ, hΓclass, hΓmax⟩ := exists_regularFamily_maximum_lt g e he hemb ξ (half_pos hε)
  obtain ⟨V, hV⟩ := exists_regular_family_lipschitz_bound g e he hemb hi
    (fun k => (Γ k).val) ((continuous_regularContractibleLoop_iff e he₁ Γ).mp Γ.continuous)
  let Γ₀ := regularSphereFamilyInclusion e he₁ hemb Γ
  obtain ⟨S, hs, H, hCr, harea, _⟩ := exists_smooth_family_leastArea_approximation g e he hemb
    Γ₀ V hV (half_pos hε)
  refine ⟨S, hs, ?_, ?_, hCr⟩
  · change LoopFamily.classOf (regularSphereFamilyInclusion e he₁ hemb S) = ξ
    exact ((LoopFamily.classOf_eq_iff _ _).mpr ⟨H.symm⟩).trans hΓclass
  · obtain ⟨k, hk⟩ := regularFamilyMaximum_attained g e he hemb hi S
    have heq : (⟨Γ₀ k, V, hV k⟩ : lipschitzContractibleLoop g) =
        regularContractibleToLipschitz g (Γ k) := by
      apply Subtype.ext
      rfl
    have ha := harea k
    rw [heq] at ha
    change |regularLeastArea g (S k) - regularLeastArea g (Γ k)| < ε / 2 at ha
    have hle := regularLeastArea_le_familyMaximum g e he hemb hi Γ k
    have hdiff := (abs_lt.mp ha).2
    linarith

end DifferentialGeometry.Geometry
