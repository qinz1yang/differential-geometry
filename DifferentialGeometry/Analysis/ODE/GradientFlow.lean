import DifferentialGeometry.Analysis.ODE.IntegralCurveTransport
import DifferentialGeometry.Geometry.Operator.Operators

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE

open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem hasDerivAt_comp_integralCurve_gradientFun
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    {γ : Real → M}
    (hγ : IsMIntegralCurve γ (fun x ↦ gradientFun (I := I) g f x))
    (t : Real) :
    HasDerivAt (f ∘ γ)
      (g.inner (γ t) (gradientFun (I := I) g f (γ t))
        (gradientFun (I := I) g f (γ t))) t := by
  have h := hasDerivAt_df_comp_integralCurve
    (I := I) f hf (fun x ↦ gradientFun (I := I) g f x) hγ t
  change HasDerivAt (f ∘ γ)
    (mvfderiv (I := I) f (γ t) (gradientFun (I := I) g f (γ t))) t at h
  convert h using 1
  exact inner_gradientFun (I := I) g f (γ t)
    (gradientFun (I := I) g f (γ t))

end DifferentialGeometry.Analysis.ODE
