import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

open Set Metric

namespace GC146ExportReview

theorem compact_comparison_target_net
    {A K : Type*} [MetricSpace A] [MetricSpace K]
    (Φ : A → K) (hΦ : ∀ a b, dist a b ≤ dist (Φ a) (Φ b))
    {η : ℝ} (hη : 0 < η) (N : ℕ) (S : Finset K) (hS : S.card ≤ N)
    (hnet : ∀ k : K, ∃ z ∈ S, dist k z ≤ η / 3) :
    ∃ T : Finset A, T.card ≤ N ∧ ∀ a : A, ∃ b ∈ T, dist a b < η := by
  classical
  have hinj : Function.Injective Φ := by
    intro a b hab
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa only [hab, dist_self] using hΦ a b) dist_nonneg
  obtain ⟨T, hcard, _, hcover⟩ :=
    Metric.exists_finset_net_card_le_of_packing (s := univ) hη N (by
      intro F _ hsep
      have hsep' : ((F.image Φ : Finset K) : Set K).Pairwise
          (fun a b => η ≤ dist a b) := by
        intro u hu v hv huv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
        exact (hsep ha hb (fun hab => huv (congrArg Φ hab))).trans (hΦ a b)
      have hc := Metric.card_le_card_of_separated_net (F.image Φ) S
        (by linarith : 2 * (η / 3) < η) hsep' (fun a _ => hnet a)
      rw [Finset.card_image_of_injective F hinj] at hc
      exact hc.trans hS)
  exact ⟨T, hcard, fun a => hcover a (mem_univ a)⟩

-- Literal original blueprint assumptions, checked as an unnamed export application.
example {A K : Type*} [MetricSpace A] [MetricSpace K] [Nonempty A] [CompactSpace K]
    (Φ : A → K) (hΦ : ∀ a b, dist a b ≤ dist (Φ a) (Φ b))
    {η : ℝ} (hη : 0 < η) (N : ℕ) (S : Finset K) (hS : S.card ≤ N)
    (hnet : ∀ k : K, ∃ z ∈ S, dist k z ≤ η / 3) :
    ∃ T : Finset A, T.card ≤ N ∧ ∀ a : A, ∃ b ∈ T, dist a b < η :=
  compact_comparison_target_net Φ hΦ hη N S hS hnet

end GC146ExportReview
