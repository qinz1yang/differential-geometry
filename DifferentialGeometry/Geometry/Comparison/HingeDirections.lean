import DifferentialGeometry.Geometry.Comparison.HingeModel
import DifferentialGeometry.Geometry.Metric.SpaceOfDirections
import DifferentialGeometry.Geometry.Comparison.GermCurvatureIndependence

set_option autoImplicit false

open Set Filter Topology

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

def leftRepresentative (H : MinimizingHinge p q) (ha : 0 < dist H.center p) :
    GeodesicRepresentative H.center where
  length := dist H.center p
  length_pos := ha
  curve := H.left
  isometry := H.left_isometry
  start := H.left_zero

def rightRepresentative (H : MinimizingHinge p q) (hb : 0 < dist H.center q) :
    GeodesicRepresentative H.center where
  length := dist H.center q
  length_pos := hb
  curve := H.right
  isometry := H.right_isometry
  start := H.right_zero

@[simp] theorem leftRepresentative_length (H : MinimizingHinge p q)
    (ha : 0 < dist H.center p) : (H.leftRepresentative ha).length = dist H.center p := rfl

@[simp] theorem rightRepresentative_length (H : MinimizingHinge p q)
    (hb : 0 < dist H.center q) : (H.rightRepresentative hb).length = dist H.center q := rfl

@[simp] theorem leftRepresentative_curve (H : MinimizingHinge p q)
    (ha : 0 < dist H.center p) : (H.leftRepresentative ha).curve = H.left := rfl

@[simp] theorem rightRepresentative_curve (H : MinimizingHinge p q)
    (hb : 0 < dist H.center q) : (H.rightRepresentative hb).curve = H.right := rfl

@[simp] theorem leftRepresentative_path (H : MinimizingHinge p q)
    (ha : 0 < dist H.center p) :
    (H.leftRepresentative ha).path = IccExtend dist_nonneg H.left := rfl

@[simp] theorem rightRepresentative_path (H : MinimizingHinge p q)
    (hb : 0 < dist H.center q) :
    (H.rightRepresentative hb).path = IccExtend dist_nonneg H.right := rfl

theorem leftRepresentative_endpoint (H : MinimizingHinge p q)
    (ha : 0 < dist H.center p) : (H.leftRepresentative ha).path (dist H.center p) = p := by
  rw [H.leftRepresentative_path ha, IccExtend_right, H.left_end]

theorem rightRepresentative_endpoint (H : MinimizingHinge p q)
    (hb : 0 < dist H.center q) : (H.rightRepresentative hb).path (dist H.center q) = q := by
  rw [H.rightRepresentative_path hb, IccExtend_right, H.right_end]

@[simp] theorem leftRepresentative_reverse (H : MinimizingHinge p q)
    (hb : 0 < dist H.center q) : H.reverse.leftRepresentative hb = H.rightRepresentative hb := rfl

@[simp] theorem rightRepresentative_reverse (H : MinimizingHinge p q)
    (ha : 0 < dist H.center p) : H.reverse.rightRepresentative ha = H.leftRepresentative ha := rfl

theorem germAngle_eq_dist_directions (H : MinimizingHinge p q) [HasAnglesAt H.center]
    {κ : ℝ} (hκ : 0 ≤ κ) (ha : 0 < dist H.center p) (hb : 0 < dist H.center q) :
    H.germAngle κ = dist (H.leftRepresentative ha).direction (H.rightRepresentative hb).direction := by
  have hzero := (H.leftRepresentative ha).tendsto_comparisonAngle_dist_direction
    (H.rightRepresentative hb)
  have hdiff := tendsto_comparisonAngleNegCurvature_sub_curvature_zero_of_radial
    hκ ha hb H.center (IccExtend dist_nonneg H.left) (IccExtend dist_nonneg H.right)
    (fun _ ht => H.left_radial ⟨ht.1.le, ht.2⟩)
    (fun _ ht => H.right_radial ⟨ht.1.le, ht.2⟩)
  apply germComparisonAngle_eq_of_tendsto
  simpa only [H.leftRepresentative_path ha, H.rightRepresentative_path hb,
    sub_add_cancel, zero_add] using hdiff.add hzero

end Metric.MinimizingHinge
