import DifferentialGeometry.Topology.LoopSpace.RegularSmoothing



noncomputable section

open Set Function ContinuousMap Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]





theorem exists_uniform_regular_smoothing_lift
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (r : F → M) (U : Set F) (hU : IsOpen U) (heU : range e ⊆ U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U) (hleft : ∀ q, r (e q) = q)
    (Γ : C(K, freeLoop M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ →
      ∀ H : unitInterval × K → freeLoop M,
        (∀ τ k θ, H (τ, k) θ = r (e (Γ k θ) + (τ : ℝ) •
          (averagedLoop φ ((⟨e, he.continuous⟩ : C(M, F)).comp (Γ k)) θ - e (Γ k θ)))) →
        ∀ Γ₁ : K → regularLoop E M,
          Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] Γ₁ →
          (∀ k, (Γ₁ k).val = Γ k) →
          ∃ R : unitInterval × K → regularLoop E M,
            Continuous[inferInstance, regularLoopTopology e (he.of_le (by exact_mod_cast le_top))] R ∧
            (∀ p, (R p).val = H p) ∧
            (∀ k, regularLoopDist e (he.of_le (by exact_mod_cast le_top)) (R (1, k)) (Γ₁ k) < ε) := by
  classical
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  by_cases hreg : ∃ Γ₀ : K → regularLoop E M,
      Continuous[inferInstance, regularLoopTopology e he₁] Γ₀ ∧ ∀ k, (Γ₀ k).val = Γ k
  · obtain ⟨Γ₀, hΓ₀, hval₀⟩ := hreg
    obtain ⟨δ, hδ, hS⟩ := exists_uniform_regular_retracted_loop_homotopy
      e he hemb r U hU heU hr hleft Γ₀ hΓ₀ hε
    refine ⟨δ, hδ, fun φ hφ H hformula Γ₁ _ hval₁ => ?_⟩
    obtain ⟨R, hR, _, _, hd, _, _, hRformula⟩ := hS φ hφ
    have heq : Γ₀ = Γ₁ := by
      funext k
      exact Subtype.ext ((hval₀ k).trans (hval₁ k).symm)
    have hAeq (k : K) : regularLoopValue e he₁ (Γ₀ k) =
        (⟨e, he.continuous⟩ : C(M, F)).comp (Γ k) := by
      apply ContinuousMap.ext
      intro θ
      change e ((Γ₀ k).val θ) = e (Γ k θ)
      rw [hval₀]
    refine ⟨R, hR, ?_, ?_⟩
    · rintro ⟨τ, k⟩
      apply ContinuousMap.ext
      intro θ
      rw [hRformula, hformula, hAeq, hval₀]
    · simpa only [heq] using hd
  · exact ⟨1, zero_lt_one, fun _ _ _ _ Γ₁ hΓ₁ hval₁ =>
      False.elim (hreg ⟨Γ₁, hΓ₁, hval₁⟩)⟩

end DifferentialGeometry.Topology
