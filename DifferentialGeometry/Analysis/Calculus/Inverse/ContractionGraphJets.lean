import DifferentialGeometry.Analysis.Calculus.Inverse.ContractionGraph
import DifferentialGeometry.Analysis.Calculus.Inverse.GraphJetBounds
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u v

theorem exists_uniform_contraction_graph_jets (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (N : Type u) (E : Type v)
        [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (U : Set E) (W : Set (E × N)), IsOpen U → IsOpen W →
        ∀ r δ : ℝ, 0 < r → 0 ≤ δ → δ ≤ 1 →
        U ×ˢ Metric.closedBall (0 : N) r ⊆ W →
        ∀ e : E × N → N, ContDiffOn ℝ (max m 1 : ℕ) e W →
        (∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r, ‖e (t, z)‖ ≤ r / 4) →
        (∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
          ‖fderiv ℝ (fun w : N => e (t, w)) z‖ ≤ 1 / 2) →
        (∀ p ∈ W, ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i e p‖ ≤ C * δ) →
        ∃ g : E → N, ContDiffOn ℝ (max m 1 : ℕ) g U ∧
          (∀ t ∈ U, ‖g t‖ ≤ r / 4 ∧ g t + e (t, g t) = 0) ∧
          (∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
            z + e (t, z) = 0 ↔ z = g t) ∧
          ∀ t ∈ U, ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g t‖ ≤ B * δ := by
  obtain ⟨B, hB, hjet⟩ := exists_bound_normal_graph_jets.{u,v} m C hC
  refine ⟨B, hB, ?_⟩
  intro N E _ _ _ _ _ _ U W hU hW r δ hr hδ0 hδ1 hcylinder e he hsmall hnormal herr
  have hn : ((max m 1 : ℕ) : ℕ∞ω) ≠ 0 := by
    have hpos : 0 < max m 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    exact_mod_cast hpos.ne'
  obtain ⟨g, hg, hvalue, huniq⟩ := exists_contDiffOn_contraction_graph
    hn hU hW hr hcylinder he hsmall hnormal
  refine ⟨g, hg, hvalue, huniq, ?_⟩
  let swap : N × E ≃ₗᵢ[ℝ] E × N := LinearIsometryEquiv.prodComm ℝ N E
  let e' : N × E → N := e ∘ swap
  intro t ht
  have hmem : g t ∈ Metric.closedBall (0 : N) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hvalue t ht).1.trans (by linarith)
  have hp : (t, g t) ∈ W := hcylinder ⟨ht, hmem⟩
  have he' : ContDiffAt ℝ (max m 1 : ℕ) e' (g t, t) := by
    change ContDiffAt ℝ (max m 1 : ℕ) (fun p : N × E => e (p.2, p.1)) (g t, t)
    exact (he.contDiffAt (hW.mem_nhds hp)).comp (g t, t)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hrel : ∀ᶠ y in 𝓝 t, g y + e' (g y, y) = 0 := by
    filter_upwards [hU.mem_nhds ht] with y hy
    exact (hvalue y hy).2
  have hnorm : ‖fderiv ℝ (fun n : N => e' (n, t)) (g t)‖ ≤ 1 / 2 :=
    hnormal t ht (g t) hmem
  apply hjet N E e' g t he' (hg.contDiffAt (hU.mem_nhds ht)) hrel hnorm δ hδ0 hδ1
  intro i hi
  change ‖iteratedFDeriv ℝ i (e ∘ swap) (g t, t)‖ ≤ C * δ
  rw [swap.norm_iteratedFDeriv_comp_right]
  exact herr (t, g t) hp i hi

end DifferentialGeometry.Analysis
