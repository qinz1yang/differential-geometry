import DifferentialGeometry.Analysis.Calculus.Inverse.ScaledContractionGraphJets

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u v

theorem exists_uniform_allOrder_scaled_contraction_graph_jets
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ (N : Type u) (E : Type v)
        [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (U : Set E) (W : Set (E × N)), IsOpen U → IsOpen W →
        ∀ r δ : ℝ, 0 < r → 0 ≤ δ → δ ≤ 1 →
        U ×ˢ closedBall (0 : N) r ⊆ W →
        ∀ e : E × N → N, ContDiffOn ℝ ∞ e W →
        (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r, ‖e (t,z)‖ ≤ r / 4) →
        (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r,
          ‖fderiv ℝ (fun w : N => e (t,w)) z‖ ≤ 1 / 2) →
        (∀ m, ∀ p ∈ W, ∀ j, j ≤ m →
          ‖iteratedFDeriv ℝ j e p‖ ≤ C m * δ * r * (r⁻¹)^j) →
        ∃ g : E → N, ContDiffOn ℝ ∞ g U ∧
          (∀ t ∈ U, ‖g t‖ ≤ r / 4 ∧ g t + e (t,g t) = 0) ∧
          (∀ t ∈ U, ∀ z ∈ closedBall (0 : N) r,
            z + e (t,z) = 0 ↔ z = g t) ∧
          ∀ m, ∀ t ∈ U, ∀ j, j ≤ m →
            ‖iteratedFDeriv ℝ j g t‖ ≤ B m * δ * r * (r⁻¹)^j := by
  classical
  have hfinite := fun m => exists_uniform_scaled_contraction_graph_jets.{u,v} m (C m) (hC m)
  choose B hB hbound using hfinite
  refine ⟨B, hB, ?_⟩
  intro N E _ _ _ _ _ _ U W hU hW r δ hr hδ0 hδ1 hcylinder e he hsmall hnormal herr
  obtain ⟨g, hg, hvalue, huniq⟩ := exists_contDiffOn_contraction_graph
    (by simp : (∞ : ℕ∞ω) ≠ 0) hU hW hr hcylinder he hsmall hnormal
  refine ⟨g, hg, hvalue, huniq, ?_⟩
  intro m
  have hem : ContDiffOn ℝ (max m 1 : ℕ) e W := he.of_le (by simp)
  obtain ⟨gm, _hgm, hvaluem, _huniqm, hjetm⟩ :=
    hbound m N E U W hU hW r δ hr hδ0 hδ1 hcylinder e hem hsmall hnormal (herr m)
  have heq (t : E) (ht : t ∈ U) : gm t = g t := by
    have hmem : gm t ∈ closedBall (0 : N) r := by
      rw [mem_closedBall, dist_zero_right]
      exact (hvaluem t ht).1.trans (by linarith)
    exact (huniq t ht (gm t) hmem).mp (hvaluem t ht).2
  intro t ht j hj
  have hevent : gm =ᶠ[𝓝 t] g := by
    filter_upwards [hU.mem_nhds ht] with y hy
    exact heq y hy
  have hderiv : iteratedFDeriv ℝ j gm t = iteratedFDeriv ℝ j g t :=
    (hevent.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds
  rw [← hderiv]
  exact hjetm t ht j hj

end DifferentialGeometry.Analysis
