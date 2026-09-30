import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

namespace GC146ExportReview

theorem expanding_open_interval_net :
    ∃ T : Finset (Ioo (0 : ℝ) 1), T.card ≤ 2 ∧
      ∀ a : Ioo (0 : ℝ) 1, ∃ b ∈ T, dist a b < 3 := by
  let Φ : Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 2 := fun a =>
    ⟨2 * a.val, by constructor <;> linarith [a.property.1, a.property.2]⟩
  let z : Icc (0 : ℝ) 2 := ⟨0, by constructor <;> norm_num⟩
  let w : Icc (0 : ℝ) 2 := ⟨2, by constructor <;> norm_num⟩
  let S : Finset (Icc (0 : ℝ) 2) := {z, w}
  apply compact_comparison_target_net (η := 3) Φ ?_ (by norm_num) 2 S ?_ ?_
  · intro a b
    change |a.val - b.val| ≤ |2 * a.val - 2 * b.val|
    rw [show 2 * a.val - 2 * b.val = 2 * (a.val - b.val) by ring, abs_mul]
    norm_num
    linarith [abs_nonneg (a.val - b.val)]
  · exact (Finset.card_insert_le z {w}).trans (by simp)
  · intro k
    by_cases hk : k.val ≤ 1
    · refine ⟨z, by simp [S], ?_⟩
      change |k.val - 0| ≤ (3 : ℝ) / 3
      simpa only [sub_zero, abs_of_nonneg k.property.1, div_self (by norm_num : (3 : ℝ) ≠ 0)] using hk
    · refine ⟨w, by simp [S], ?_⟩
      change |k.val - 2| ≤ (3 : ℝ) / 3
      rw [abs_of_nonpos (by linarith [k.property.2])]
      norm_num
      linarith

end GC146ExportReview
