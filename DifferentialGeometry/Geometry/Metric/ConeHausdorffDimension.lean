import DifferentialGeometry.Geometry.Metric.ConeRadialParametrization
import DifferentialGeometry.Topology.MetricSpace.IntervalProductDimension

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

theorem dimH_univ_le_dimH_base_add_one {Y : Type*} [MetricSpace Y] :
    dimH (univ : Set (EuclideanCone Y)) ≤ dimH (univ : Set Y) + 1 := by
  classical
  rcases isEmpty_or_nonempty Y with hempty | hnonempty
  · have hsub : (univ : Set (EuclideanCone Y)).Subsingleton := by
      intro x _ y _
      rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, _⟩
      · rcases eq_tip_or_eq_mk y with rfl | ⟨s, v, _, _⟩
        · rfl
        · exact isEmptyElim v
      · exact isEmptyElim u
    rw [hsub.dimH_zero]
    exact zero_le
  · have hball (B : ℝ≥0) :
        dimH (closedBall (tip : EuclideanCone Y) (B : ℝ)) ≤ dimH (univ : Set Y) + 1 := by
      let e : Icc (0 : ℝ) (B : ℝ) × Y → ℝ × Y := fun z => (z.1.val, z.2)
      have he : Isometry e := by
        apply Isometry.of_dist_eq
        intro x y
        rfl
      have himage : e '' (univ : Set (Icc (0 : ℝ) (B : ℝ) × Y)) =
          (Icc (0 : ℝ) (B : ℝ)) ×ˢ (univ : Set Y) := by
        ext z
        constructor
        · rintro ⟨⟨r, u⟩, _, rfl⟩
          exact ⟨r.property, mem_univ _⟩
        · rintro ⟨hr, _⟩
          exact ⟨(⟨z.1, hr⟩, z.2), mem_univ _, rfl⟩
      have hdom : dimH (univ : Set (Icc (0 : ℝ) (B : ℝ) × Y)) =
          dimH ((Icc (0 : ℝ) (B : ℝ)) ×ˢ (univ : Set Y)) := by
        rw [← he.dimH_image, himage]
      have hbound := (lipschitzWith_bounded_mk (Y := Y) B).dimH_range_le
      rw [range_bounded_mk] at hbound
      exact hbound.trans (hdom.le.trans (dimH_Icc_prod_le_add_one (univ : Set Y) B.property))
    rw [← iUnion_closedBall_nat (tip : EuclideanCone Y), dimH_iUnion]
    apply iSup_le
    intro k
    simpa only [NNReal.coe_natCast] using hball (k : ℝ≥0)

end Metric.EuclideanCone
