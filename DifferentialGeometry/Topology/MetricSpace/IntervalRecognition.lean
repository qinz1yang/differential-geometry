import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_pointed_interval_or_half_interval_of_isOpen_segments [Nontrivial X]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b})) (p : X) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : X) = p) ∨
      (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : X) = p) := by
  classical
  by_cases hm : ∃ (a b : ℝ) (σ : Icc a b → X), Isometry σ ∧
      ∃ t : Icc a b, a < (t : ℝ) ∧ (t : ℝ) < b ∧ σ t = p
  · obtain ⟨a, b, σ, hσ, t, hat, htb, htp⟩ := hm
    rcases htp with rfl
    have hr : 0 < min ((t : ℝ) - a) (b - t) :=
      lt_min (sub_pos.mpr hat) (sub_pos.mpr htb)
    exact ⟨_, hr, Or.inl (exists_pointed_interval_isometry_of_isOpen_segment
      hsegments hσ (hopen a b σ hσ) t hr le_rfl)⟩
  · have hp : ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p := by
      apply (metric_endpoint_iff_not_mem_segment_interior hsegments p).mpr
      intro a b σ hσ t hat htb htp
      exact hm ⟨a, b, σ, hσ, t, hat, htb, htp⟩
    obtain ⟨y, hyp⟩ := exists_ne p
    obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments p y
    obtain ⟨σ, hσ, hσ0, _⟩ := exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
    have hD : 0 < dist p y := dist_pos.mpr hyp.symm
    have hh := exists_pointed_half_interval_isometry_of_isOpen_segment hsegments hD.le hσ
      (hopen 0 (dist p y) σ hσ) (by simpa only [hσ0] using hp) hD le_rfl
    rw [hσ0] at hh
    exact ⟨dist p y, hD, Or.inr hh⟩

end Metric
