import DifferentialGeometry.Geometry.Metric.Conformal.Connection
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]

theorem divergence_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    {X : (x : M) → TangentSpace I x} {x : M} (hX : MDiffAt (T% X) x) :
    divergence (LeviCivita (conformalMetric g u)) X x =
      divergence (LeviCivita g) X x + (Module.finrank Real E : Real) *
        mvfderiv I (u : M → Real) x (X x) := by
  have heq : (LeviCivita (conformalMetric g u) X x).toLinearMap =
      (LeviCivita g X x).toLinearMap +
      (mvfderiv I (u : M → Real) x).toLinearMap.smulRight (X x) +
      mvfderiv I (u : M → Real) x (X x) • LinearMap.id -
      (g.inner x (X x)).toLinearMap.smulRight (gradientFun g u x) := by
    ext v
    change LeviCivita (conformalMetric g u) X x v = _
    rw [LeviCivita_conformalMetric g u hX]
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe]
    rw [g.symm x v (X x)]
  unfold divergence
  rw [heq]
  simp only [map_sub, map_add, map_smul, LinearMap.trace_smulRight,
    LinearMap.trace_id, smul_eq_mul, ContinuousLinearMap.coe_coe]
  rw [g.symm x (X x) (gradientFun g u x), inner_gradientFun]
  change _ = _ + (Module.finrank Real (TangentSpace I x) : Real) * _
  ring

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] in
private theorem mvfderiv_exp_neg_two_mul_apply
    (u : C^∞⟮I, M; Real⟯) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => Real.exp (-(2 * u y))) x v =
      -2 * Real.exp (-(2 * u x)) * mvfderiv I (u : M → Real) x v := by
  have hu := (u.contMDiff.mdifferentiableAt (by simp) :
    MDifferentiableAt I 𝓘(Real) (u : M → Real) x).hasMFDerivAt
  have htwo : HasMFDerivAt I 𝓘(Real) (fun y : M => -(2 * u y)) x
      ((-2 : Real) • mvfderiv I (u : M → Real) x) := by
    have heq : (fun y : M => -(2 * u y)) = (-2 : Real) • (u : M → Real) := by
      funext y
      change -(2 * u y) = -2 * u y
      ring
    rw [heq]
    exact hu.const_smul (-2)
  have hx := ((Real.hasDerivAt_exp (-(2 * u x))).hasFDerivAt.hasMFDerivAt.comp x htwo).mfderiv
  have happly := congrArg (fun F : TangentSpace I x →L[Real] Real => F v) hx
  change mvfderiv I (fun y => Real.exp (-(2 * u y))) x v =
    (-2 * mvfderiv I (u : M → Real) x v) * Real.exp (-(2 * u x)) at happly
  rw [happly]
  ring

theorem laplacian_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    {f : M → Real} {x : M} (hf : ContMDiffAt I 𝓘(Real) 2 f x) :
    laplacian (LeviCivita (conformalMetric g u)) (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) * (laplacian (LeviCivita g) g f x +
        ((Module.finrank Real E : Real) - 2) *
          g.inner x (gradientFun g u x) (gradientFun g f x)) := by
  have hgrad := (gradientFun_contMDiffAt_one (conformalMetric g u) hf).mdifferentiableAt one_ne_zero
  rw [laplacian, divergence_conformalMetric g u hgrad]
  have hG : gradientFun (conformalMetric g u) f =
      (fun y => Real.exp (-(2 * u y))) • gradientFun g f := by
    funext y
    exact gradientFun_conformalMetric g u f y
  rw [hG]
  have hc : MDiffAt (fun y : M => Real.exp (-(2 * u y))) x :=
    (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff).neg).mdifferentiableAt
      (by simp)
  rw [divergence_smul (LeviCivita g) inferInstance hc ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero),
    mvfderiv_exp_neg_two_mul_apply]
  change _ + (Module.finrank Real E : Real) *
    mvfderiv I (u : M → Real) x (Real.exp (-(2 * u x)) • gradientFun g f x) = _
  rw [map_smul, smul_eq_mul, inner_gradientFun]
  change _ = Real.exp (-(2 * u x)) * (divergence (LeviCivita g) (gradientFun g f) x + _)
  ring

theorem laplacian_conformalMetric_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (hn : Module.finrank Real E = 2)
    {f : M → Real} {x : M} (hf : ContMDiffAt I 𝓘(Real) 2 f x) :
    laplacian (LeviCivita (conformalMetric g u)) (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) * laplacian (LeviCivita g) g f x := by
  rw [laplacian_conformalMetric g u hf, hn]
  norm_num

end DifferentialGeometry.Geometry.Operator
