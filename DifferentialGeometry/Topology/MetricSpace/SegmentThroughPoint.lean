import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_isometric_segment_through_of_dist_add_eq
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {x z y : X} (hxy : dist x z + dist z y = dist x y) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → X, Isometry σ ∧
      σ ⟨0, le_rfl, dist_nonneg⟩ = x ∧ σ ⟨dist x y, dist_nonneg, le_rfl⟩ = y ∧
      σ ⟨dist x z, dist_nonneg, by linarith [dist_nonneg (x := z) (y := y)]⟩ = z := by
  obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments x z
  obtain ⟨g, _, hg0, hg1, hgd⟩ := hsegments z y
  obtain ⟨α, hα, hα0, hα1⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  obtain ⟨β, hβ, hβ0, hβ1⟩ := exists_isometric_segment_of_dist_eq_mul hg0 hg1 hgd
  obtain ⟨σ, hσ, hl, hr⟩ := exists_isometric_segment_concat
    (dist_nonneg (x := x) (y := z)) (dist_nonneg (x := z) (y := y)) hα hβ
    (hα1.trans hβ0.symm) (by rw [hα0, hβ1]; exact hxy.symm)
  have hσ0 := (hl ⟨0, le_rfl, dist_nonneg⟩).trans hα0
  have hσ1 := (hr ⟨dist z y, dist_nonneg, le_rfl⟩).trans hβ1
  have hσz := (hl ⟨dist x z, dist_nonneg, le_rfl⟩).trans hα1
  let τ : Icc (0 : ℝ) (dist x y) → X := fun t =>
    σ ⟨t, t.property.1, by linarith [t.property.2]⟩
  refine ⟨τ, Isometry.of_dist_eq (fun s t => hσ.dist_eq _ _), hσ0, ?_, hσz⟩
  change σ ⟨dist x y, dist_nonneg, hxy.ge⟩ = y
  exact (congrArg σ (Subtype.ext hxy.symm)).trans hσ1

end Metric
