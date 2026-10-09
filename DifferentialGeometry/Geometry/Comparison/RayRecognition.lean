import DifferentialGeometry.Geometry.Comparison.RayCoordinate
import DifferentialGeometry.Topology.MetricSpace.LineOrRayModel
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem exists_line_or_ray_isometry_of_isometric_ray_of_open_segments
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {γ : Ici (0 : ℝ) → X} (hγ : Isometry γ) :
    (∃ e : X ≃ᵢ ℝ, e (γ ⟨0, by simp⟩) = 0 ∧ ∀ t, e (γ t) = (t : ℝ)) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ),
      (e (γ ⟨0, by simp⟩) : ℝ) = a ∧ ∀ t, (e (γ t) : ℝ) = (t : ℝ) + a) := by
  have hcurves : ∀ x : X, ∃ c : unitInterval → X,
      Continuous c ∧ c 0 = γ ⟨0, by simp⟩ ∧ c 1 = x := by
    intro x
    obtain ⟨c, hc, hc0, hc1, _⟩ := hsegments (γ ⟨0, by simp⟩) x
    exact ⟨c, hc, hc0, hc1⟩
  have hrange : Ici (0 : ℝ) ⊆ range (raySignedDistance γ) := by
    intro t ht
    exact ⟨γ ⟨t, ht⟩, raySignedDistance_apply_isometry hγ _⟩
  have h := exists_line_or_ray_isometry_of_isometry_range
    (isometry_raySignedDistance hκ hcomp hsegments hopen hγ)
    (raySignedDistance_apply_isometry hγ ⟨0, by simp⟩) hrange hcurves
  rcases h with ⟨e, he0, he⟩ | ⟨a, ha, e, he0, he⟩
  · refine Or.inl ⟨e, he0, ?_⟩
    intro t
    rw [he, raySignedDistance_apply_isometry hγ]
  · refine Or.inr ⟨a, ha, e, he0, ?_⟩
    intro t
    rw [he, raySignedDistance_apply_isometry hγ]

theorem exists_line_or_ray_isometry_of_isometric_ray_of_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1)
    {γ : Ici (0 : ℝ) → X} (hγ : Isometry γ) :
    (∃ e : X ≃ᵢ ℝ, e (γ ⟨0, by simp⟩) = 0 ∧ ∀ t, e (γ t) = (t : ℝ)) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ),
      (e (γ ⟨0, by simp⟩) : ℝ) = a ∧ ∀ t, (e (γ t) : ℝ) = (t : ℝ) + a) := by
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hopen := isOpen_segment_image_of_dimH_le_one hcurves hcomp
    (fun z => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hdim
  exact exists_line_or_ray_isometry_of_isometric_ray_of_open_segments
    le_rfl hcomp hsegments hopen hγ

end DifferentialGeometry.Geometry.Comparison.Toponogov
