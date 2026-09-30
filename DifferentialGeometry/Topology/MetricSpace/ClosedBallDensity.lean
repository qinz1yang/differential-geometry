import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem closedBall_subset_closure_ball_of_segments
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {p : X} {R : ℝ} (hR : 0 < R) : closedBall p R ⊆ closure (ball p R) := by
  intro z hz
  by_cases hzp : z = p
  · subst z
    exact subset_closure (mem_ball_self hR)
  have hD : 0 < dist p z := dist_pos.mpr (Ne.symm hzp)
  have hDR : dist p z ≤ R := by simpa only [mem_closedBall, dist_comm] using hz
  obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments p z
  obtain ⟨σ, hσ, hσ0, hσD⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ := min (dist p z / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (half_pos hD) (half_pos hε)
  have hδD : δ < dist p z := (min_le_left _ _).trans_lt (half_lt_self hD)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  let s : Icc (0 : ℝ) (dist p z) := ⟨dist p z - δ, by constructor <;> linarith⟩
  have hsp : dist (σ s) p = dist p z - δ := by
    calc
      dist (σ s) p = dist (σ s) (σ ⟨0, le_rfl, hD.le⟩) := congrArg (dist (σ s)) hσ0.symm
      _ = dist s ⟨0, le_rfl, hD.le⟩ := hσ.dist_eq _ _
      _ = dist p z - δ := by
        simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, s]
        exact abs_of_nonneg (by linarith)
  have hzs : dist z (σ s) = δ := by
    calc
      dist z (σ s) = dist (σ ⟨dist p z, hD.le, le_rfl⟩) (σ s) :=
        congrArg (fun w => dist w (σ s)) hσD.symm
      _ = dist (⟨dist p z, hD.le, le_rfl⟩ : Icc (0 : ℝ) (dist p z)) s := hσ.dist_eq _ _
      _ = δ := by
        simp only [Subtype.dist_eq, Real.dist_eq, s]
        have he : dist p z - (dist p z - δ) = δ := by ring
        rw [he, abs_of_pos hδ]
  exact ⟨σ s, by rw [mem_ball, hsp]; linarith, by rw [hzs]; exact hδε⟩

end Metric
