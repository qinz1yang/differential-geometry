import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {f : ℝ → ℝ} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_scalar_comp (x : M)
    (hf : DifferentiableAt ℝ f (u x)) (hu : MDifferentiableAt I 𝓘(ℝ) u x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y => f (u y)) x v = deriv f (u x) * mvfderiv I u x v := by
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I)
    (f := u) (g := f) x hf.mdifferentiableAt hu v
  rw [mvfderiv_real_model_eq_fderiv, hf.hasDerivAt.hasFDerivAt.fderiv,
    ← mvfderiv_real_eq_mfderiv I u x v] at h
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, mul_comm] using h

variable [I.Boundaryless]

theorem hessFun_comp (g : SmoothRiemannianMetric I M)
    (hf : ContDiff ℝ ∞ f) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (x : M) (v w : TangentSpace I x) :
    hessFun g (fun y => f (u y)) x v w =
      deriv (deriv f) (u x) * mvfderiv I u x v * mvfderiv I u x w +
        deriv f (u x) * hessFun g u x v w := by
  have hcomp : ContMDiff I 𝓘(ℝ) ∞ (fun y => f (u y)) := hf.contMDiff.comp hu
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hgrad : (fun y : M => gradFun g (fun z => f (u z)) y) =
      (fun y : M => deriv f (u y)) • (fun y : M => gradFun g u y) := by
    funext y
    exact gradientFun_comp g ((hf.differentiable (by simp)) (u y))
      (hu.mdifferentiable (by simp) y)
  have hgu := (gradFun_contMDiff_total g hu).mdifferentiable (by simp) x
  have hcoeff : MDifferentiableAt I 𝓘(ℝ) (fun y => deriv f (u y)) x :=
    (hd.contMDiff.comp hu).mdifferentiable (by simp) x
  have hc := congrArg (fun L => L v)
    ((LeviCivita g).isCovariantDerivativeOnUniv.leibniz hgu hcoeff)
  change (LeviCivita g).toFun
    ((fun y : M => deriv f (u y)) • (fun y : M => gradFun g u y)) x v = _ at hc
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at hc
  change _ = deriv f (u x) • (LeviCivita g).toFun (fun y : M => gradFun g u y) x v +
    mvfderiv I (fun y => deriv f (u y)) x v • gradFun g u x at hc
  rw [differential_scalar_comp x ((hd.differentiable (by simp)) (u x))
    (hu.mdifferentiable (by simp) x)] at hc
  rw [hessFun_eq_cov_grad g hcomp, hgrad, hc]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [← hessFun_eq_cov_grad g hu x v w, inner_gradFun]
  change deriv f (u x) * hessFun g u x v w +
    deriv (deriv f) (u x) * mvfderiv I u x v * mvfderiv I u x w = _
  ring

end DifferentialGeometry.Geometry.Operator
