import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nontrivial X]

theorem exists_diameter_isometric_segment
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t) :
    ∃ D : ℝ, 0 < D ∧ ∃ σ : Icc (0 : ℝ) D → X,
      Isometry σ ∧ ∀ x y : X, dist x y ≤ D := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  obtain ⟨z, _, hz⟩ := (isCompact_univ : IsCompact (univ : Set (X × X))).exists_isMaxOn
    ⟨(a, b), mem_univ _⟩ (continuous_fst.dist continuous_snd).continuousOn
  have hmax (x y : X) : dist x y ≤ dist z.1 z.2 := hz (mem_univ (x, y))
  have hD : 0 < dist z.1 z.2 := (dist_pos.mpr hab).trans_le (hmax a b)
  obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments z.1 z.2
  obtain ⟨σ, hσ, _, _⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  exact ⟨dist z.1 z.2, hD, σ, hσ, hmax⟩

end Metric
