import DifferentialGeometry.Topology.LoopSpace.RegularHomotopy
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction



noncomputable section

open Set Function ContinuousMap Manifold Metric
open scoped Topology ContDiff Manifold

universe u

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [Nonempty M]




theorem exists_regular_nearby_homotopy_radius (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ η : ℝ, 0 < η ∧ ∀ (K : Type u) [TopologicalSpace K]
      (Γ Δ : K → regularLoop E M),
      Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ →
      Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Δ →
      (∀ k θ, dist (e ((Δ k).val θ)) (e ((Γ k).val θ)) < η) →
      ∃ R : unitInterval × K → regularLoop E M,
        Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] R ∧
        (∀ k, R (0, k) = Γ k) ∧ (∀ k, R (1, k) = Δ k) ∧
        (∀ k, Γ k = Δ k → ∀ τ, R (τ, k) = Γ k) := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction he hemb hi
  obtain ⟨η, hη, hηU⟩ := (isCompact_range he.continuous).exists_cthickening_subset_open hU heU
  refine ⟨η, hη, fun K _ Γ Δ hΓ hΔ hclose => ?_⟩
  obtain ⟨hcB, hdB⟩ := (continuous_regularLoop_iff e he₁ Δ).mp hΔ
  let B : C(K, freeLoop F) := ⟨fun k => regularLoopValue e he₁ (Δ k),
    (FreeLoop.continuous_family_iff _).mpr hcB⟩
  have hregion (τ : unitInterval) (k : K) (θ : loopCircle) :
      e ((Γ k).val θ) + (τ : ℝ) • (B k θ - e ((Γ k).val θ)) ∈ U := by
    apply hηU
    apply mem_cthickening_of_dist_le _ (e ((Γ k).val θ)) η (range e) (mem_range_self _)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg τ.property.1]
    exact ((mul_le_of_le_one_left (norm_nonneg _) τ.property.2).trans_lt
      (by simpa only [dist_eq_norm] using! hclose k θ)).le
  obtain ⟨R, hc, hformula, hz, ho⟩ := exists_regular_affine_homotopy e he₁ hU
    (hr.of_le (by exact_mod_cast le_top)) hleft Γ hΓ B
    (fun k => regularLoop_embedded_contDiff e he₁ (Δ k)) hdB hregion
  refine ⟨R, hc, hz, ?_, ?_⟩
  · intro k
    apply Subtype.ext
    apply ContinuousMap.ext
    intro θ
    rw [ho]
    exact hleft _
  · intro k hk τ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro θ
    rw [hformula]
    change r (e ((Γ k).val θ) + (τ : ℝ) • (e ((Δ k).val θ) - e ((Γ k).val θ))) = _
    rw [← hk, sub_self, smul_zero, add_zero, hleft]

end DifferentialGeometry.Topology
