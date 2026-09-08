import DifferentialGeometry.Geometry.Metric.WarpedProduct
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Analysis.Calculus.RoundCylindricalProfile

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.RoundCylindrical

open DifferentialGeometry.Analysis.RoundCylindricalProfile

def positiveRay : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩

abbrev PolarSpace (n : ℕ) :=
  positiveRay × Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

private local instance sphereDimension (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by simp⟩

private def rayMetric : SmoothRiemannianMetric 𝓘(ℝ, ℝ) positiveRay :=
  (flatModelMetric ℝ).restrictOpen positiveRay

private theorem rayMetric_inner (x : positiveRay) (v w : ℝ) :
    rayMetric.inner x v w = v * w := by
  change w * v = v * w
  ring

def metric (n : ℕ) : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 n)) (PolarSpace n) :=
  rayMetric.warpedProduct (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n))
    (fun r : positiveRay => radius (r : ℝ))
    (contDiff_radius.contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (U := positiveRay)))
    (fun r => radius_pos r.property)

theorem metric_inner (n : ℕ) (x : PolarSpace n)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) x) :
    (metric n).inner x v w =
      v.1 * w.1 + radius (x.1 : ℝ) ^ 2 *
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)).inner x.2 v.2 w.2 := by
  apply Eq.trans (SmoothRiemannianMetric.warpedProduct_inner _ _ _ _ _ x v w)
  rw [rayMetric_inner]

def cylinderMetric (n : ℕ) : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 n)) (PolarSpace n) :=
  rayMetric.prod (scaleMetric 4 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)))

theorem cylinderMetric_inner (n : ℕ) (x : PolarSpace n)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) x) :
    (cylinderMetric n).inner x v w =
      v.1 * w.1 + 4 *
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)).inner x.2 v.2 w.2 := by
  apply Eq.trans (SmoothRiemannianMetric.prod_inner _ _ x v w)
  change rayMetric.inner x.1 v.1 w.1 + 4 * _ = _
  rw [rayMetric_inner]
  rfl

theorem metric_inner_eq_cylinderMetric_of_transitionEnd_le (n : ℕ) {x : PolarSpace n}
    (hx : transitionEnd ≤ (x.1 : ℝ))
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) x) :
    (metric n).inner x v w = (cylinderMetric n).inner x v w := by
  rw [metric_inner, cylinderMetric_inner, radius_eq_cylinderRadius_of_le hx]
  norm_num [cylinderRadius]

end DifferentialGeometry.Geometry.RoundCylindrical
