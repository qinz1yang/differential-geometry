import DifferentialGeometry.Topology.LoopSpace.RegularNearby
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz



noncomputable section

open Set Function ContinuousMap Manifold Metric DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal NNReal

universe u

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [Nonempty M]



theorem exists_regular_metric_nearby_homotopy_radius
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (K : Type u) [TopologicalSpace K]
      (Γ Δ : K → regularLoop E M),
      Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ →
      Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Δ →
      (∀ k θ, riemannianEDistOf g ((Δ k).val θ) ((Γ k).val θ) < ENNReal.ofReal ε) →
      ∃ R : unitInterval × K → regularLoop E M,
        Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] R ∧
        (∀ k, R (0, k) = Γ k) ∧ (∀ k, R (1, k) = Δ k) ∧
        (∀ k, Γ k = Δ k → ∀ τ, R (τ, k) = Γ k) := by
  obtain ⟨η, hη, hR⟩ := exists_regular_nearby_homotopy_radius e he hemb hi
  obtain ⟨C, hC, hLip⟩ := DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff g
    (he.of_le (by exact_mod_cast le_top))
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  refine ⟨η / C, div_pos hη hCr, fun K _ Γ Δ hΓ hΔ hclose => hR K Γ Δ hΓ hΔ ?_⟩
  intro k θ
  have h := (hLip ((Δ k).val θ) ((Γ k).val θ)).trans_lt
    (ENNReal.mul_lt_mul_right (by exact_mod_cast hC.ne') ENNReal.coe_ne_top (hclose k θ))
  have hmul : (C : ℝ≥0∞) * ENNReal.ofReal (η / C) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    congr 1
    field_simp
  rw [hmul, edist_dist] at h
  exact (ENNReal.ofReal_lt_ofReal_iff hη).mp h

end DifferentialGeometry.Topology
