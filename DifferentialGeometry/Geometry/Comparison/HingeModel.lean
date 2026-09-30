import DifferentialGeometry.Topology.MetricSpace.MinimizingHinge
import DifferentialGeometry.Geometry.Comparison.EndpointHingeComparison
import DifferentialGeometry.Geometry.Comparison.ModelSideOrder

set_option autoImplicit false

open Set

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

noncomputable def germAngle (H : MinimizingHinge p q) (κ : ℝ) : ℝ :=
  germComparisonAngle κ (IccExtend dist_nonneg H.left) (IccExtend dist_nonneg H.right)

noncomputable def modelSide (H : MinimizingHinge p q) (κ : ℝ) : ℝ :=
  modelSideNegCurvature κ (dist H.center p) (dist H.center q) (H.germAngle κ)

theorem germAngle_mem_Icc (H : MinimizingHinge p q) (κ : ℝ) :
    H.germAngle κ ∈ Icc (0 : ℝ) Real.pi := germComparisonAngle_mem_Icc _ _ _

theorem germAngle_reverse (H : MinimizingHinge p q) (κ : ℝ) :
    H.reverse.germAngle κ = H.germAngle κ := germComparisonAngle_comm _ _ _

theorem modelSide_reverse (H : MinimizingHinge p q) (κ : ℝ) :
    H.reverse.modelSide κ = H.modelSide κ := by
  rw [modelSide, H.germAngle_reverse]
  exact modelSideNegCurvature_comm _ _ _ _

theorem modelSide_nonneg (H : MinimizingHinge p q) (κ : ℝ) : 0 ≤ H.modelSide κ :=
  modelSideNegCurvature_nonneg dist_nonneg dist_nonneg

theorem modelSide_of_center_eq_left (H : MinimizingHinge p q) {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : H.center = p) : H.modelSide κ = dist p q := by
  rw [modelSide, hp, dist_self, modelSideNegCurvature_zero_left hκ dist_nonneg]

theorem modelSide_of_center_eq_right (H : MinimizingHinge p q) {κ : ℝ} (hκ : 0 ≤ κ)
    (hq : H.center = q) : H.modelSide κ = dist p q := by
  rw [← H.modelSide_reverse κ, H.reverse.modelSide_of_center_eq_left hκ hq, dist_comm]

theorem modelSide_ge_dist_of_endpoint_comparison (H : MinimizingHinge p q)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hsmall : endpointHingeComparison κ p r)
    (hsum : dist H.center p + dist H.center q < r) : dist p q ≤ H.modelSide κ := by
  by_cases hp : H.center = p
  · rw [H.modelSide_of_center_eq_left hκ hp]
  by_cases hq : H.center = q
  · rw [H.modelSide_of_center_eq_right hκ hq]
  have h := hsmall.modelSide_ge_dist hκ (dist_pos.mpr hp) (dist_pos.mpr hq) hsum
    (γ := IccExtend dist_nonneg H.left) (β := IccExtend dist_nonneg H.right)
    (by rw [IccExtend_right, H.left_end])
    (fun s hs => H.left_radial ⟨hs.1.le, hs.2⟩)
    (fun s hs => H.right_radial ⟨hs.1.le, hs.2⟩)
    (fun s hs t ht => H.left_dist ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun s hs t ht => H.right_dist ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
  rwa [IccExtend_right, H.right_end] at h

end Metric.MinimizingHinge
namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem modelSide_sorted (H : MinimizingHinge p q) (κ : ℝ) :
    modelSideNegCurvature κ (min (dist H.center p) (dist H.center q))
      (max (dist H.center p) (dist H.center q)) (H.germAngle κ) = H.modelSide κ := by
  by_cases h : dist H.center p ≤ dist H.center q
  · rw [min_eq_left h, max_eq_right h]
    rfl
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
    exact modelSideNegCurvature_comm _ _ _ _

end Metric.MinimizingHinge

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem short_right_comparison (H : MinimizingHinge p q) {κ r h : ℝ}
    (hsmall : endpointHingeComparison κ p r) (ha : 0 < dist H.center p)
    (hh : 0 < h) (hhb : h ≤ dist H.center q)
    (hshort : dist H.center p + h < r) :
    comparisonAngleNegCurvature κ (dist H.center p) h
      (dist (H.right ⟨h, ⟨hh.le, hhb⟩⟩) p) ≤ H.germAngle κ := by
  have ht := hsmall H.center (dist H.center p) h
    (IccExtend dist_nonneg H.left) (IccExtend dist_nonneg H.right) ha hh hshort
    (by rw [IccExtend_right, H.left_end])
    (fun s hs => H.left_radial ⟨hs.1.le, hs.2⟩)
    (fun s hs => H.right_radial ⟨hs.1.le, hs.2.trans hhb⟩)
    (fun s hs t ht => H.left_dist ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun s hs t ht => H.right_dist ⟨hs.1.le, hs.2.trans hhb⟩ ⟨ht.1.le, ht.2.trans hhb⟩)
  rwa [IccExtend_of_mem dist_nonneg H.right ⟨hh.le, hhb⟩, dist_comm p] at ht

end Metric.MinimizingHinge

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem comparisonAngle_le_iff_dist_le_modelSide (H : MinimizingHinge p q)
    {κ : ℝ} (hκ : 0 ≤ κ) (ha : 0 < dist H.center p) (hb : 0 < dist H.center q) :
    comparisonAngleNegCurvature κ (dist H.center p) (dist H.center q) (dist p q) ≤
      H.germAngle κ ↔ dist p q ≤ H.modelSide κ := by
  have hlo := abs_dist_sub_le p q H.center
  rw [dist_comm p H.center, dist_comm q H.center] at hlo
  have hhi := dist_triangle p H.center q
  rw [dist_comm p H.center] at hhi
  exact comparisonAngleNegCurvature_le_iff_le_modelSide hκ ha hb hlo hhi (H.germAngle_mem_Icc κ)

end Metric.MinimizingHinge
