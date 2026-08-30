import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
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
              ((g.inner x) (metricSharp (I := I) g x alpha)) w =
                alpha w := by
            exact inner_metricSharp (I := I) g x alpha w
          symm
          calc
            (scaleMetric (I := I) c hc g).inner x
                (c⁻¹ • metricSharp (I := I) g x alpha) w =
                c * (c⁻¹ *
                  ((g.inner x) (metricSharp (I := I) g x alpha)) w) := by
                  rw [scaleMetric_inner]
                  simp only [metricSharp, map_smul, FunLike.coe_smul,
                    Pi.smul_apply, smul_eq_mul]
            _ = c * (c⁻¹ * alpha w) :=
                congrArg (fun z : Real => c * (c⁻¹ * z)) hinner
            _ = alpha w := by
                field_simp [ne_of_gt hc]


theorem gradientFun_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    gradientFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ • gradientFun (I := I) g f x := by
  change metricSharp (I := I) (scaleMetric (I := I) c hc g) x
      (mvfderiv (I := I) f x).toLinearMap =
    c⁻¹ • metricSharp (I := I) g x (mvfderiv (I := I) f x).toLinearMap
  exact metricSharp_scaleMetric (I := I) c hc g x
    (mvfderiv (I := I) f x).toLinearMap

theorem laplacian_scaleMetric
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) f x =
      c⁻¹ * laplacian (I := I) cov g f x := by
  have hgrad_eq :
      gradientFun (I := I) (scaleMetric (I := I) c hc g) f =
        c⁻¹ • gradientFun (I := I) g f := by
    funext y
    exact gradientFun_scale (I := I) c hc g f y
  calc
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) f x =
        divergence (I := I) cov (c⁻¹ • gradientFun (I := I) g f) x := by
          simp [laplacian, hgrad_eq]
    _ = c⁻¹ * laplacian (I := I) cov g f x := by
          simpa [laplacian] using
            divergence_const_smul (I := I) cov inferInstance c⁻¹ hgrad

theorem laplacian_scaleMetric_const_smul
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) (c⁻¹ • f) x =
      c⁻¹ * c⁻¹ * laplacian (I := I) cov g f x := by
  have hgradScaled :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (scaleMetric (I := I) c hc g) f y) x := by
    have hscale :
        MDiffAt (T% fun y : M =>
          c⁻¹ • gradientFun (I := I) g f y) x := by
      simpa [Pi.smul_apply] using
        (mdifferentiableAt_const (I := I) (c := c⁻¹)).smul_section hgrad
    have hpt : ∀ y : M,
        gradientFun (I := I) (scaleMetric (I := I) c hc g) f y =
          c⁻¹ • gradientFun (I := I) g f y := by
      intro y
      exact gradientFun_scale (I := I) c hc g f y
    have htotal :
        (T% fun y : M =>
          gradientFun (I := I) (scaleMetric (I := I) c hc g) f y) =
          (T% fun y : M => c⁻¹ • gradientFun (I := I) g f y) := by
      funext y
      rw [hpt y]
    rw [htotal]
    exact hscale
  rw [laplacian_const_smul (I := I) cov (scaleMetric (I := I) c hc g)
    c⁻¹ hf hgradScaled]
  rw [laplacian_scaleMetric (I := I) c hc cov g hgrad]
  ring

theorem metricTracePair0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) (scaleMetric (I := I) c hc g) B =
      c⁻¹ * metricTracePair0SAt (I := I) g B := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
    Real (TangentSpace I x) :=
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l (extChartAt I x x)
  have hinv : MetricInverseInBasisGen (I := I) g x basis gInv :=
    Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  have hinvScale :
      MetricInverseInBasisGen (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [metricTracePair0SAt_eq_sum_basis (I := I) (scaleMetric (I := I) c hc g)
      basis (fun i j => c⁻¹ * gInv i j) hinvScale,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end DifferentialGeometry.Geometry.Operator
