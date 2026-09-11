import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_add_of_local_regularity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g f y) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g h y) x) :
    laplacian cov g (fun y => f y + h y) x =
      laplacian cov g f x + laplacian cov g h x := by
  have he : gradientFun (I := I) g (fun y => f y + h y) =ᶠ[𝓝 x]
      gradientFun (I := I) g f + gradientFun (I := I) g h := by
    filter_upwards [hf, hh] with y hfy hhy
    exact gradientFun_add g hfy hhy
  have hr := mdifferentiableAt_add_section hgf hgh
  have hl : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g (fun z => f z + h z) y) x := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) hy
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hl hr univ_mem he
  calc
    laplacian cov g (fun y => f y + h y) x =
        divergence cov (gradientFun (I := I) g f + gradientFun (I := I) g h) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = laplacian cov g f x + laplacian cov g h x :=
      divergence_add cov inferInstance hgf hgh

end DifferentialGeometry.Geometry.Operator

end
