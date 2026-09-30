import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Metric

theorem exists_isometry_segment_of_germ {X : Type*} [MetricSpace X]
    {R : ℝ} (hR : 0 ≤ R) {x : X} {γ : ℝ → X}
    (hrad : ∀ s ∈ Ioc (0 : ℝ) R, dist x (γ s) = s)
    (hmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|) :
    ∃ σ : Icc (0 : ℝ) R → X, Isometry σ ∧ σ ⟨0, ⟨le_rfl, hR⟩⟩ = x ∧
      ∀ s (hs : s ∈ Ioc (0 : ℝ) R), σ ⟨s, ⟨hs.1.le, hs.2⟩⟩ = γ s := by
  classical
  let σ : Icc (0 : ℝ) R → X := fun t => if (t : ℝ) = 0 then x else γ t
  have heq (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) : σ ⟨s, ⟨hs.1.le, hs.2⟩⟩ = γ s := by
    simp only [σ, ite_eq_right hs.1.ne']
  refine ⟨σ, ?_, by simp [σ], heq⟩
  apply Isometry.of_dist_eq
  intro s t
  by_cases hs : (s : ℝ) = 0
  · by_cases ht : (t : ℝ) = 0
    · simp only [σ, hs, ht, ite_eq_left, dist_self, Subtype.dist_eq]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      simp only [σ, hs, ht, ite_eq_left, Subtype.dist_eq, Real.dist_eq,
        zero_sub, abs_neg, abs_of_pos htpos]
      exact hrad t ⟨htpos, t.property.2⟩
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (Ne.symm hs)
    by_cases ht : (t : ℝ) = 0
    · simp only [σ, hs, ht, ite_eq_left, Subtype.dist_eq, Real.dist_eq,
        sub_zero, abs_of_pos hspos]
      rw [dist_comm]
      exact hrad s ⟨hspos, s.property.2⟩
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      simp only [σ, hs, ht, Subtype.dist_eq, Real.dist_eq]
      exact hmin s ⟨hspos, s.property.2⟩ t ⟨htpos, t.property.2⟩

end Metric
