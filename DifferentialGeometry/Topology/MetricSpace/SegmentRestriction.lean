import DifferentialGeometry.Topology.MetricSpace.SegmentExtension

set_option autoImplicit false

open Set Metric

namespace Isometry

variable {X : Type*} [MetricSpace X] {a b h : ℝ} {σ : Icc a b → X}

theorem IccExtend_forward_isometry (hσ : Isometry σ) (hh : h ∈ Icc a b) :
    Isometry (fun s : Icc (0 : ℝ) (b - h) => IccExtend (hh.1.trans hh.2) σ (h + s)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [hσ.IccExtend_forward_dist hh s.property t.property, Subtype.dist_eq, Real.dist_eq]

theorem IccExtend_backward_isometry (hσ : Isometry σ) (hh : h ∈ Icc a b) :
    Isometry (fun s : Icc (0 : ℝ) (h - a) => IccExtend (hh.1.trans hh.2) σ (h - s)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [hσ.IccExtend_backward_dist hh s.property t.property, Subtype.dist_eq, Real.dist_eq]

end Isometry
