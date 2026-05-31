import RicciFlower.Metric.Scaling
import RicciFlower.Operators

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Constant scaling of realized scalar operators

This file contains the gradient scaling law used by parabolic rescaling.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem metricSharp_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha =
      c⁻¹ • metricSharp (I := I) g x alpha := by
  apply metricFlatLinear_injective (I := I) (scaleMetric (I := I) c hc g) x
  ext w
  simp only [metricFlatLinear_apply]
  calc
    (scaleMetric (I := I) c hc g).inner x
        (metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha) w =
        alpha w := inner_metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha w
    _ =
        (scaleMetric (I := I) c hc g).inner x
          (c⁻¹ • metricSharp (I := I) g x alpha) w := by
          have hinner :
              ((g.inner x) ((metricFlatEquiv (I := I) g x).symm alpha)) w =
                alpha w := by
            simpa [metricSharp] using inner_metricSharp (I := I) g x alpha w
          symm
          calc
            (scaleMetric (I := I) c hc g).inner x
                (c⁻¹ • metricSharp (I := I) g x alpha) w =
                c * (c⁻¹ *
                  ((g.inner x) ((metricFlatEquiv (I := I) g x).symm alpha)) w) := by
                  rw [scaleMetric_inner]
                  simp only [metricSharp, map_smul, ContinuousLinearMap.coe_smul',
                    Pi.smul_apply, smul_eq_mul]
            _ = c * (c⁻¹ * alpha w) :=
                congrArg (fun z : Real => c * (c⁻¹ * z)) hinner
            _ = alpha w := by
                field_simp [ne_of_gt hc]

/-- Under a positive constant metric scaling, gradients scale by `c⁻¹`. -/
theorem gradientFun_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    gradientFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ • gradientFun (I := I) g f x := by
  simpa [gradientFun] using
    metricSharp_scaleMetric (I := I) c hc g x
      (mfderiv I 𝓘(Real, Real) f x).toLinearMap

end

end Realized
end RicciFlower
