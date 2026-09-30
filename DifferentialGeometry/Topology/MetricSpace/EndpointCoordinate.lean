import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood
import DifferentialGeometry.Topology.MetricSpace.ClosedBallDensity

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem closedBall_eq_segment_range_at_endpoint_of_isOpen
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 < D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hend : ∀ x y : X, dist x (σ ⟨0, le_rfl, hD.le⟩) + dist (σ ⟨0, le_rfl, hD.le⟩) y = dist x y →
      x = σ ⟨0, le_rfl, hD.le⟩ ∨ y = σ ⟨0, le_rfl, hD.le⟩) :
    closedBall (σ ⟨0, le_rfl, hD.le⟩) D = range σ := by
  have hb : ball (σ ⟨0, le_rfl, hD.le⟩) D ⊆ range σ := by
    rw [ball_eq_segment_image_at_endpoint_of_isOpen hsegments hD.le hσ ho hend le_rfl]
    exact image_subset_range _ _
  apply Subset.antisymm
  · exact (closedBall_subset_closure_ball_of_segments hsegments hD).trans
      (closure_minimal hb (isCompact_range hσ.continuous).isClosed)
  · rintro z ⟨t, rfl⟩
    rw [mem_closedBall, hσ.dist_eq]
    simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] using t.property.2


theorem isometry_dist_from_endpoint_of_isOpen_segments
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b})) {p : X}
    (hend : ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p) :
    Isometry (fun x : X => dist p x) := by
  have hd (x y : X) (hxy : dist p x ≤ dist p y) :
      dist (dist p x) (dist p y) = dist x y := by
    by_cases hyp : y = p
    · subst y
      have hxp : x = p := (dist_eq_zero.mp (le_antisymm (by simpa using hxy) dist_nonneg)).symm
      subst x
      simp
    have hD : 0 < dist p y := dist_pos.mpr (Ne.symm hyp)
    obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments p y
    obtain ⟨σ, hσ, hσ0, hσD⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
    have hend' : ∀ u v : X, dist u (σ ⟨0, le_rfl, hD.le⟩) +
        dist (σ ⟨0, le_rfl, hD.le⟩) v = dist u v →
        u = σ ⟨0, le_rfl, hD.le⟩ ∨ v = σ ⟨0, le_rfl, hD.le⟩ := by
      simpa only [hσ0] using hend
    have hb := closedBall_eq_segment_range_at_endpoint_of_isOpen hsegments hD hσ
      (hopen 0 (dist p y) σ hσ) hend'
    have hx : x ∈ range σ := by
      rw [← hb, hσ0, mem_closedBall, dist_comm]
      exact hxy
    obtain ⟨s, hs⟩ := hx
    have hps : dist p x = (s : ℝ) := by
      calc
        dist p x = dist (σ ⟨0, le_rfl, hD.le⟩) (σ s) := by rw [hσ0, hs]
        _ = dist (⟨0, le_rfl, hD.le⟩ : Icc (0 : ℝ) (dist p y)) s := hσ.dist_eq _ _
        _ = (s : ℝ) := by simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg s.property.1]
    calc
      dist (dist p x) (dist p y) = dist s (⟨dist p y, hD.le, le_rfl⟩ : Icc (0 : ℝ) (dist p y)) := by
        rw [hps]; rfl
      _ = dist (σ s) (σ ⟨dist p y, hD.le, le_rfl⟩) := (hσ.dist_eq _ _).symm
      _ = dist x y := by rw [hs, hσD]
  apply Isometry.of_dist_eq
  intro x y
  rcases le_total (dist p x) (dist p y) with hxy | hyx
  · exact hd x y hxy
  · simpa only [dist_comm] using hd y x hyx

end Metric
