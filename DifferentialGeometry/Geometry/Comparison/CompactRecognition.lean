import DifferentialGeometry.Geometry.Comparison.DiameterCircleIsometry
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
import DifferentialGeometry.Topology.MetricSpace.DiameterSegmentExistence

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nontrivial X]

theorem exists_interval_or_circle_isometry_of_compact_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) (p : X) :
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : X ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ AddCircle L, e p = 0) := by
  classical
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hopen := isOpen_segment_image_of_dimH_le_one hcurves hcomp
    (fun z => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hdim
  obtain ⟨D, hD, σ, hσ, hdiam⟩ := exists_diameter_isometric_segment hsegments
  by_cases hsurj : Function.Surjective σ
  · let f : Icc (0 : ℝ) D ≃ᵢ X := ⟨Equiv.ofBijective σ ⟨hσ.injective, hsurj⟩, hσ⟩
    exact Or.inl ⟨D, hD, (f.symm p : ℝ), (f.symm p).property, f.symm, rfl⟩
  · have hout : ∃ x : X, x ∉ range σ := by
      by_contra hn
      apply hsurj
      intro x
      by_contra hx
      exact hn ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hout
    obtain ⟨e, _⟩ := exists_circle_isometry_of_outside_diameter_segment
      (le_refl (0 : ℝ)) hcomp hsegments hD hσ (hopen 0 D σ hσ) hdiam hx
    let f := e.trans (IsometryEquiv.subRight (e p))
    refine Or.inr ⟨2 * D, by linarith, f, ?_⟩
    change e p - e p = 0
    exact sub_self _

end DifferentialGeometry.Geometry.Comparison.Toponogov
