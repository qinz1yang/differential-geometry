import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

open Set Function Topology Filter
set_option autoImplicit false
namespace DifferentialGeometry.Topology

theorem exists_shorter_strip_image_subset
    {B M : Type*} [TopologicalSpace B] [CompactSpace B] [TopologicalSpace M]
    {ε : ℝ} (hε : 0 < ε) {c : B × Icc (0 : ℝ) ε → M} (hc : Continuous c)
    {W : Set M} (hW : IsOpen W)
    (hzero : ∀ b, c (b, ⟨0, ⟨le_rfl, hε.le⟩⟩) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ c '' {q | (q.2 : ℝ) < δ} ⊆ W := by
  let zero : Icc (0 : ℝ) ε := ⟨0, ⟨le_rfl, hε.le⟩⟩
  obtain ⟨U, V, _, hV, hBU, h0V, hUV⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set B)) (isCompact_singleton : IsCompact {zero})
    (hW.preimage hc) (by
      rintro ⟨b, t⟩ ⟨_, ht⟩
      rw [mem_singleton_iff] at ht
      change t = zero at ht
      subst t
      exact hzero b)
  obtain ⟨R, hR, hRV⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
  have h0R : (0 : ℝ) ∈ R := by
    have hh : zero ∈ V := h0V (mem_singleton _)
    rw [← hRV] at hh
    exact hh
  obtain ⟨r, hr, hrR⟩ := Metric.mem_nhds_iff.mp (hR.mem_nhds h0R)
  let δ := min (ε / 2) (r / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδε, ?_⟩
  rintro y ⟨⟨b, t⟩, ht, rfl⟩
  apply hUV ⟨hBU (mem_univ b), ?_⟩
  rw [← hRV]
  apply hrR
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
  exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (by linarith))

end DifferentialGeometry.Topology
