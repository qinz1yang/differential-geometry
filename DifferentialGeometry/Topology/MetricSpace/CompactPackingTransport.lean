import DifferentialGeometry.Topology.MetricSpace.FinitePacking
import DifferentialGeometry.Topology.MetricSpace.FiniteNets

set_option autoImplicit false

open Set

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem totallyBounded_of_finite_transport_to_compact {S : Set X} {T : Set Y}
    (hT : IsCompact T) {K : ℝ} (hK : 0 < K)
    (himages : ∀ ε : ℝ, 0 < ε → ∀ A : Finset X, (A : Set X) ⊆ S →
      (A : Set X).Pairwise (fun x y => ε ≤ dist x y) →
      ∃ B : Finset Y, (B : Set Y) ⊆ T ∧ A.card ≤ B.card ∧
        (B : Set Y).Pairwise (fun x y => K * ε ≤ dist x y)) : TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hKε : 0 < K * ε := mul_pos hK hε
  obtain ⟨F, hFT, hFnet⟩ := exists_finset_net_of_isCompact hT
    (show 0 < K * ε / 3 by positivity)
  have hpack (A : Finset X) (hA : (A : Set X) ⊆ S)
      (hsep : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)) : A.card ≤ F.card := by
    obtain ⟨B, hBT, hcard, hsepB⟩ := himages ε hε A hA hsep
    apply hcard.trans
    exact card_le_card_of_separated_net B F (show 2 * (K * ε / 3) < K * ε by linarith)
      hsepB (fun b hb => hFnet b (hBT hb))
  obtain ⟨A, _, _, hnet⟩ := exists_finset_net_card_le_of_packing hε F.card hpack
  refine ⟨A, A.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hnet x hx
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy⟩⟩

end Metric
