import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Tensor0SBundle

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem metricInvBasis_conformal
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv) :
    MetricInverseInBasis_gen (I := I) (conformalMetric f hf g) x basis
      (fun i j => Real.exp (-(2 * f x)) * gInv i j) := by
  intro i k
  have hcancel : Real.exp (-(2 * f x)) * Real.exp (2 * f x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  constructor
  · calc
      ∑ j, (Real.exp (-(2 * f x)) * gInv i j) *
          (conformalMetric f hf g).inner x (basis j) (basis k)
          = ∑ j, gInv i j * g.inner x (basis j) (basis k) := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hstep :
                (Real.exp (-(2 * f x)) * gInv i j) *
                    (conformalMetric f hf g).inner x (basis j) (basis k) =
                  gInv i j * g.inner x (basis j) (basis k) := by
              rw [conformalMetric_inner]
              have hrw :
                  Real.exp (-(2 * f x)) * gInv i j *
                      (Real.exp (2 * f x) * g.inner x (basis j) (basis k)) =
                    (Real.exp (-(2 * f x)) * Real.exp (2 * f x)) *
                      (gInv i j * g.inner x (basis j) (basis k)) := by ring
              rw [hrw, hcancel, one_mul]
            exact hstep
      _ = if i = k then 1 else 0 := (hinv i k).1
  · calc
      ∑ j, (conformalMetric f hf g).inner x (basis i) (basis j) *
          (Real.exp (-(2 * f x)) * gInv j k)
          = ∑ j, g.inner x (basis i) (basis j) * gInv j k := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hstep :
                (conformalMetric f hf g).inner x (basis i) (basis j) *
                    (Real.exp (-(2 * f x)) * gInv j k) =
                  g.inner x (basis i) (basis j) * gInv j k := by
              rw [conformalMetric_inner]
              have hrw :
                  Real.exp (2 * f x) * g.inner x (basis i) (basis j) *
                      (Real.exp (-(2 * f x)) * gInv j k) =
                    (Real.exp (-(2 * f x)) * Real.exp (2 * f x)) *
                      (g.inner x (basis i) (basis j) * gInv j k) := by ring
              rw [hrw, hcancel, one_mul]
            exact hstep
      _ = if i = k then 1 else 0 := (hinv i k).2


theorem inner0S_conformal
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {x : M} (s : Nat)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    inner0S (I := I) (conformalMetric f hf g) x s A B =
      Real.exp (-(2 * s * f x)) * inner0S (I := I) g x s A B := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx
      (𝕜 := Real) E) Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hinvConf :
      MetricInverseInBasis_gen (I := I) (conformalMetric f hf g) x basis
        (fun i j => Real.exp (-(2 * f x)) * gInv i j) :=
    metricInvBasis_conformal (I := I) f hf g basis gInv hinv
  have hexp : Real.exp (-(2 * s * f x)) = (Real.exp (-(2 * f x))) ^ s := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [inner0S_eq_coord (I := I) (conformalMetric f hf g) x s basis
      (fun i j => Real.exp (-(2 * f x)) * gInv i j) hinvConf A B,
    inner0S_eq_coord (I := I) g x s basis gInv hinv A B, hexp]
  unfold coordInner0S
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring


theorem normSq0S_conformal
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {x : M} (s : Nat)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    normSq0S (I := I) (conformalMetric f hf g) x s T =
      Real.exp (-(2 * s * f x)) * normSq0S (I := I) g x s T := by
  rw [normSq0S_eq_inner, normSq0S_eq_inner,
    inner0S_conformal (I := I) f hf g s T T]


theorem metricTensor0S_conformal
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Integral.Connection.metricTensor0S (I := I)
        (conformalMetric f hf g) x =
      Real.exp (2 * f x) •
        DifferentialGeometry.Integral.Connection.metricTensor0S (I := I) g x := by
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  show DifferentialGeometry.Integral.Connection.metricTensor0S (I := I)
        (conformalMetric f hf g) x v
      = Real.exp (2 * f x) *
        DifferentialGeometry.Integral.Connection.metricTensor0S (I := I) g x v
  rw [DifferentialGeometry.Integral.Connection.metricTensor0S_apply,
    DifferentialGeometry.Integral.Connection.metricTensor0S_apply, conformalMetric_inner]


end

end Tensor0SBundle
