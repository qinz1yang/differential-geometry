import DifferentialGeometry.Topology.MetricSpace.EndpointCoordinate
import DifferentialGeometry.Topology.MetricSpace.EndpointModel
import DifferentialGeometry.Topology.MetricSpace.HalfIntervalEndpoint
import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]

theorem exists_interval_or_ray_isometry_of_endpoint_of_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) {p : X}
    (hend : ∀ x y : X, dist x p + dist p y = dist x y → x = p ∨ y = p) :
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ Icc (0 : ℝ) L, ∀ x, (e x : ℝ) = dist p x) ∨
    (∃ e : X ≃ᵢ Ici (0 : ℝ), ∀ x, (e x : ℝ) = dist p x) := by
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hopen := isOpen_segment_image_of_dimH_le_one hcurves hcomp
    (fun z => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hdim
  have hiso := isometry_dist_from_endpoint_of_isOpen_segments hsegments hopen hend
  apply exists_interval_or_ray_isometry_of_isometry_dist _ hiso
  intro x
  obtain ⟨c, hc, hc0, hc1, _⟩ := hcurves p x 1 zero_lt_one
  exact ⟨c, hc, hc0, hc1⟩

theorem exists_interval_or_ray_isometry_of_half_interval_chart_of_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) {p : X} {r : ℝ} (hr : 0 < r)
    (e : Ico (0 : ℝ) r ≃ᵢ ball p r) (he0 : (e ⟨0, le_rfl, hr⟩ : X) = p) :
    (∃ L : ℝ, 0 < L ∧ ∃ f : X ≃ᵢ Icc (0 : ℝ) L, ∀ x, (f x : ℝ) = dist p x) ∨
    (∃ f : X ≃ᵢ Ici (0 : ℝ), ∀ x, (f x : ℝ) = dist p x) :=
  exists_interval_or_ray_isometry_of_endpoint_of_dimH_le_one hsegments hcomp hdim
    (metric_endpoint_of_pointed_half_interval_chart hsegments hr e he0)

end DifferentialGeometry.Geometry.Comparison.Toponogov
