import DifferentialGeometry.Topology.MetricSpace.NoncompactRay
import DifferentialGeometry.Geometry.Comparison.RayRecognition
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalProperness

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem exists_line_or_ray_isometry_of_not_isCompact_of_dimH_le_one
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1)
    (hnot : ¬ IsCompact (univ : Set X)) (p : X) :
    (∃ e : X ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) := by
  let : ProperSpace X := properSpace_of_local_comparison_and_dimH hcurves
    (le_refl (0 : ℝ)) (n := 1) (by simpa using hdim)
    (fun q => ⟨univ, isOpen_univ, hcomp, mem_univ q⟩)
  have hsegments := exists_metric_segment_of_approximate_midpoints
    (approximate_midpoints_of_arbitrarily_short_curves hcurves)
  obtain ⟨r, hr, hr0⟩ := exists_isometric_ray_of_not_isCompact hsegments hnot p
  rcases exists_line_or_ray_isometry_of_isometric_ray_of_dimH_le_one
      hsegments hcomp hdim hr with ⟨e, he0, _⟩ | ⟨a, ha, e, he0, _⟩
  · exact Or.inl ⟨e, hr0 ▸ he0⟩
  · exact Or.inr ⟨a, ha, e, hr0 ▸ he0⟩

theorem exists_line_or_ray_isometry_of_not_isCompact_of_geodesic_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1)
    (hnot : ¬ IsCompact (univ : Set X)) (p : X) :
    (∃ e : X ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) :=
  exists_line_or_ray_isometry_of_not_isCompact_of_dimH_le_one
    (arbitrarily_short_curves_of_metric_segments hsegments) hcomp hdim hnot p

end DifferentialGeometry.Geometry.Comparison.Toponogov
