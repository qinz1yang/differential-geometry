import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

noncomputable section
open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem differential1FormFun_comp {φ : ℝ → ℝ} {u : M → ℝ} {x : M}
    (hφ : DifferentiableAt ℝ φ (u x))
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    differential1FormFun (I := I) (fun y => φ (u y)) x =
      deriv φ (u x) • differential1FormFun (I := I) u x := by
  have hmvcomp : mvfderiv (I := I) (φ ∘ u) x =
      deriv φ (u x) • mvfderiv (I := I) u x := by
    ext v
    have hchain := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := u) (g := φ) x hφ.mdifferentiableAt hu v
    rw [mvfderiv_real_model_eq_fderiv, hφ.hasDerivAt.hasFDerivAt.fderiv,
      ← mvfderiv_real_eq_mfderiv I u x v] at hchain
    simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm] using hchain
  unfold differential1FormFun
  rw [show (fun y => φ (u y)) = φ ∘ u by rfl, hmvcomp]
  change dualToCotangentLinear (I := I)
    (deriv φ (u x) • (mvfderiv (I := I) u x).toLinearMap) = _
  exact map_smul _ _ _

theorem normSq0S_differential1FormFun_comp
    (g : SmoothRiemannianMetric I M) {φ : ℝ → ℝ} {u : M → ℝ} {x : M}
    (hφ : DifferentiableAt ℝ φ (u x))
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    normSq0S (I := I) g x 1 (differential1FormFun (I := I) (fun y => φ (u y)) x) =
      (deriv φ (u x)) ^ 2 * normSq0S (I := I) g x 1 (differential1FormFun (I := I) u x) := by
  rw [differential1FormFun_comp hφ hu, normSq0S_smul]

theorem normSq0S_differential1FormFun_exp_neg_le
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a L : ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hL : normSq0S (I := I) g x 1 (differential1FormFun (I := I) u x) ≤ L) :
    normSq0S (I := I) g x 1
      (differential1FormFun (I := I) (fun y => Real.exp (-a * u y)) x) ≤
      (a ^ 2 * L) * (Real.exp (-a * u x)) ^ 2 := by
  have hd : HasDerivAt (fun z : ℝ => Real.exp (-a * z))
      (Real.exp (-a * u x) * -a) (u x) := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (u x)).const_mul (-a)).exp
  rw [normSq0S_differential1FormFun_comp g hd.differentiableAt hu, hd.deriv]
  have hh := mul_le_mul_of_nonneg_left hL (sq_nonneg (Real.exp (-a * u x) * -a))
  nlinarith only [hh]

end DifferentialGeometry.Geometry.Operator
