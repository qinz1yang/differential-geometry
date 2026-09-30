import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood
import DifferentialGeometry.Topology.MetricSpace.ClosedBallDensity

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem closedBall_eq_segment_image_of_isOpen
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {a b : ℝ} {σ : Icc a b → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    (p : Icc a b) {r : ℝ} (hrpos : 0 < r)
    (hr : r ≤ min ((p : ℝ) - a) (b - p)) :
    closedBall (σ p) r = σ '' {t | dist t p ≤ r} := by
  have hb : ball (σ p) r ⊆ range σ := by
    rw [ball_eq_segment_image_of_isOpen hsegments hσ ho p hr]
    exact image_subset_range _ _
  have hclosed : IsClosed (range σ) := (isCompact_range hσ.continuous).isClosed
  have hsub : closedBall (σ p) r ⊆ range σ :=
    (closedBall_subset_closure_ball_of_segments hsegments hrpos).trans
      (closure_minimal hb hclosed)
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, ht⟩ := hsub hx
    refine ⟨t, ?_, ht⟩
    simpa only [mem_ofPred_eq, mem_closedBall, ← ht, hσ.dist_eq] using hx
  · rintro x ⟨t, ht, rfl⟩
    simpa only [mem_ofPred_eq, mem_closedBall, hσ.dist_eq] using ht

theorem closedBall_on_isometric_ray_of_isOpen_segments
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {γ : Ici (0 : ℝ) → X} (hγ : Isometry γ) {R : ℝ} (hR : 0 < R) :
    closedBall (γ ⟨R, hR.le⟩) R = γ '' {t | (t : ℝ) ≤ 2 * R} := by
  let σ : Icc (0 : ℝ) (2 * R) → X := fun s => γ ⟨s, s.property.1⟩
  have hσ : Isometry σ := Isometry.of_dist_eq (fun s t => hγ.dist_eq _ _)
  let p : Icc (0 : ℝ) (2 * R) := ⟨R, by constructor <;> linarith⟩
  have hp : σ p = γ ⟨R, hR.le⟩ := rfl
  have hb := closedBall_eq_segment_image_of_isOpen hsegments hσ
    (hopen 0 (2 * R) σ hσ) p hR (by dsimp [p]; apply le_min <;> linarith)
  rw [hp] at hb
  rw [hb]
  apply Subset.antisymm
  · rintro x ⟨s, _, rfl⟩
    exact ⟨⟨s, s.property.1⟩, s.property.2, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    change (t : ℝ) ≤ 2 * R at ht
    have ht0 : 0 ≤ (t : ℝ) := t.property
    refine ⟨⟨t, t.property, ht⟩, ?_, rfl⟩
    change |(t : ℝ) - R| ≤ R
    rw [abs_le]
    constructor <;> linarith

end Metric
