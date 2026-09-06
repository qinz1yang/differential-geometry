import DifferentialGeometry.Geometry.Operator.GradientRegularity

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_exp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {φ : M → ℝ} {x : M}
    (hφ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 φ x) :
    laplacian cov g (fun y => Real.exp (φ y)) x =
      Real.exp (φ x) * (laplacian cov g φ x +
        g.inner x (gradientFun g φ x) (gradientFun g φ x)) := by
  have hφn : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) φ y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hφ).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hgrad := (gradientFun_contMDiffAt_one g hφ).mdifferentiableAt one_ne_zero
  have h := laplacian_comp_at cov g Real.differentiable_exp
    (by rw [Real.deriv_exp]; exact Real.differentiable_exp.differentiableAt) hφn hgrad
  simpa only [Real.deriv_exp, mul_add] using h

theorem laplacian_exp_mul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {φ f : M → ℝ} {x : M}
    (hφ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 φ x)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    laplacian cov g (fun y => Real.exp (φ y) * f y) x =
      Real.exp (φ x) * (laplacian cov g f x +
        2 * g.inner x (gradientFun g φ x) (gradientFun g f x) +
        (laplacian cov g φ x +
          g.inner x (gradientFun g φ x) (gradientFun g φ x)) * f x) := by
  have he : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => Real.exp (φ y)) x :=
    Real.contDiff_exp.contMDiff.contMDiffAt.comp x hφ
  have hen : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => Real.exp (φ z)) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp he).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hfn : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  rw [laplacian_mul_at cov g hen hfn
    ((gradientFun_contMDiffAt_one g he).mdifferentiableAt one_ne_zero)
    ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero),
    laplacian_exp cov g hφ,
    gradientFun_comp g Real.differentiable_exp.differentiableAt
      (hφ.mdifferentiableAt (by norm_num))]
  simp only [Real.deriv_exp, map_smul, smul_apply, smul_eq_mul]
  ring

end DifferentialGeometry.Geometry.Operator
