import DifferentialGeometry.Geometry.Comparison.Volume.RadialJacobiJets
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.AlongCurveJets

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]

theorem radialJacobi_inner_second_derivative
    (g : SmoothRiemannianMetric I M) (p : M) (x v w : E) :
    iteratedDeriv 2 (fun t => g.inner (radialCurve g p x t)
      (radialJacobiField g p x v t) (radialJacobiField g p x w t)) 0 =
      2 * g.inner p v w := by
  have h := iteratedDeriv_inner g 2
    ((contMDiffAt_radialJacobiField_zero g p x v).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((contMDiffAt_radialJacobiField_zero g p x w).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine h.trans ?_
  set_option backward.isDefEq.respectTransparency false in
  norm_num only [Finset.sum_range_succ, Function.iterate_succ_apply', Function.iterate_zero_apply,
    Function.comp_apply, id_eq, radialJacobi_zero, covDerivAlong_radialJacobiField_zero,
    radialCurve_zero, map_zero, zero_apply, zero_add, add_zero, zero_mul,
    mul_zero, Nat.choose, map_neg, neg_apply, smul_zero, nsmul_eq_mul, Nat.cast_ofNat]
  exact congrArg (fun q : M => (2 : ℝ) * g.inner q v w) (radialCurve_zero g p x)

theorem radialJacobi_inner_third_derivative
    (g : SmoothRiemannianMetric I M) (p : M) (x v w : E) :
    iteratedDeriv 3 (fun t => g.inner (radialCurve g p x t)
      (radialJacobiField g p x v t) (radialJacobiField g p x w t)) 0 =
      0 := by
  have h := iteratedDeriv_inner g 3
    ((contMDiffAt_radialJacobiField_zero g p x v).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
    ((contMDiffAt_radialJacobiField_zero g p x w).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
  refine h.trans ?_
  set_option backward.isDefEq.respectTransparency false in
  norm_num only [Finset.sum_range_succ, Function.iterate_succ_apply', Function.iterate_zero_apply,
    Function.comp_apply, id_eq, radialJacobi_zero, covDerivAlong_radialJacobiField_zero,
    radialJacobiField_second_covariant_derivative_eq_zero,
    radialCurve_zero, map_zero, zero_apply, zero_add, add_zero, zero_mul,
    mul_zero, Nat.choose, map_neg, neg_apply, smul_zero, nsmul_eq_mul, Nat.cast_ofNat]

theorem radialJacobi_inner_fourth_derivative
    (g : SmoothRiemannianMetric I M) (p : M) (x v w : E) :
    iteratedDeriv 4 (fun t => g.inner (radialCurve g p x t)
      (radialJacobiField g p x v t) (radialJacobiField g p x w t)) 0 =
      -8 * g.inner p (Curvature.riemannOp (Connection.LeviCivita g) p v x x) w := by
  have h := iteratedDeriv_inner g 4
    ((contMDiffAt_radialJacobiField_zero g p x v).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
    ((contMDiffAt_radialJacobiField_zero g p x w).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4))
  refine h.trans ?_
  set_option backward.isDefEq.respectTransparency false in
  norm_num only [Finset.sum_range_succ, Function.iterate_succ_apply', Function.iterate_zero_apply,
    Function.comp_apply, id_eq, radialJacobi_zero, covDerivAlong_radialJacobiField_zero,
    radialJacobiField_second_covariant_derivative_eq_zero, radialJacobiField_third_covariant_derivative,
    radialCurve_zero, map_zero, zero_apply, zero_add, add_zero, zero_mul,
    mul_zero, Nat.choose, map_neg, neg_apply, smul_zero, nsmul_eq_mul, Nat.cast_ofNat]
  have hmetric := congrArg
    (fun q : M => (4 : ℝ) * -g.inner q v (Curvature.riemannOp (Connection.LeviCivita g) p w x x) +
      4 * -g.inner q (Curvature.riemannOp (Connection.LeviCivita g) p v x x) w)
    (radialCurve_zero g p x)
  refine hmetric.trans ?_
  have hsymm := Curvature.riemannOp_diag_symm g p x v w
  linear_combination 4 * hsymm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
