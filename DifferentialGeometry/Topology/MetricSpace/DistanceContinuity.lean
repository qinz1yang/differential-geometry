import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.MeasureTheory.Measure.OpenPos

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [MetricSpace X]

theorem min_dist_one_le_of_dense_truncated_distance_bounds
    {ι : Type*} {a : ι → X} (ha : DenseRange a) (x y : X) {c : ℝ}
    (h : ∀ i, |min (dist x (a i)) 1 - min (dist y (a i)) 1| ≤ c) :
    min (dist x y) 1 ≤ c := by
  have hc : IsClosed {p : X | |min (dist x p) 1 - min (dist y p) 1| ≤ c} :=
    isClosed_le (by fun_prop) continuous_const
  have hs : closure (range a) ⊆ {p : X | |min (dist x p) 1 - min (dist y p) 1| ≤ c} :=
    closure_minimal (by rintro p ⟨i, rfl⟩; exact h i) hc
  have hx := hs (ha x)
  simpa only [mem_ofPred_eq, dist_self, min_eq_left zero_le_one, zero_sub, abs_neg,
    abs_of_nonneg (le_min dist_nonneg zero_le_one), dist_comm y x] using hx

theorem uniformContinuous_of_truncated_distance_modulus
    {A : Type*} [PseudoMetricSpace A] {f : A → X} {ω : ℝ → ℝ}
    (hω : Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (h : ∀ x y, min (dist (f x) (f y)) 1 ≤ ω (dist x y)) :
    UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have he := hω (Iio_mem_nhds (lt_min hε zero_lt_one))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hnear : dist x y ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_of_nonneg dist_nonneg] using hxy
  have hmin : min (dist (f x) (f y)) 1 < min ε 1 := (h x y).trans_lt (hδsub hnear)
  have hdist : dist (f x) (f y) < min ε 1 := by
    rcases min_lt_iff.mp hmin with hd | hone
    · exact hd
    · exact False.elim ((not_lt_of_ge (min_le_right ε 1)) hone)
  exact hdist.trans_le (min_le_left ε 1)

theorem uniformContinuous_of_dense_truncated_distance_modulus
    {A ι : Type*} [PseudoMetricSpace A] {a : ι → X} (ha : DenseRange a)
    {f : A → X} {ω : ℝ → ℝ} (hω : Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (h : ∀ i x y, |min (dist (f x) (a i)) 1 - min (dist (f y) (a i)) 1| ≤ ω (dist x y)) :
    UniformContinuous f :=
  uniformContinuous_of_truncated_distance_modulus hω
    (fun x y => min_dist_one_le_of_dense_truncated_distance_bounds
      ha (f x) (f y) (fun i => h i x y))

end DifferentialGeometry.Topology

end

end
