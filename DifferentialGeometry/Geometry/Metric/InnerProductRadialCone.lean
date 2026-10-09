import DifferentialGeometry.Geometry.Metric.RadialConeData
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Radial cone data of a real inner product space (AC82)

A real inner product space `V` with the dilations `x ↦ t • x` is a radial metric cone at `0` in
the sense of AC82 (Blueprint 207A, `def:alexandrov-radial-cone`): the cone kernel at `0` is the
inner product, and the AC82 distance identity is the polarization identity. This is the cone of
the Euclidean models used in the LC21 cone-at-infinity packages.
-/

set_option autoImplicit false

noncomputable section
open scoped NNReal RealInnerProductSpace

namespace GC.MetricGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The AC82 cone kernel at the origin of an inner product space is the inner product. -/
theorem radialConeKernel_zero_eq_inner (x y : V) :
    radialConeKernel (0 : V) x y = ⟪x, y⟫ := by
  unfold radialConeKernel
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, zero_sub, zero_sub, norm_neg, norm_neg,
    norm_sub_sq_real]
  ring

variable (V) in
/-- AC82 radial cone data at `0` of a real inner product space, with `H_t x = t • x`. -/
def RadialConeData.ofInnerProductSpace : RadialConeData (0 : V) where
  map t x := (t : ℝ) • x
  map_zero x := by simp
  map_one x := by simp
  dist_sq s t x y := by
    rw [radialConeKernel_zero_eq_inner, dist_eq_norm, dist_eq_norm, dist_eq_norm, zero_sub,
      zero_sub, norm_neg, norm_neg, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, Real.norm_of_nonneg s.coe_nonneg, Real.norm_of_nonneg t.coe_nonneg]
    simp only [RCLike.conj_to_real]
    ring

@[simp] theorem RadialConeData.ofInnerProductSpace_map (t : ℝ≥0) (x : V) :
    (RadialConeData.ofInnerProductSpace V).map t x = (t : ℝ) • x :=
  rfl

end GC.MetricGeometry
