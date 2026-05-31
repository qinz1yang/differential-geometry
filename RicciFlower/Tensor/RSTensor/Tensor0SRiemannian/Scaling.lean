import RicciFlower.Metric.Scaling
import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Coordinate

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Constant scaling of tensor norms

This file contains tensor-fiber metric scaling facts used by parabolic
rescaling.  A constant metric scaling by `c` scales each inverse metric factor
by `c⁻¹`.
-/

namespace Tensor0SBundle

noncomputable section

open RicciFlower
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Inverse-metric components in a basis scale by `c⁻¹` under `g ↦ c g`. -/
theorem metricInvBasis_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    MetricInverseInBasis (I := I) (scaleMetric (I := I) c hc g) x basis
      (fun i j => c⁻¹ * gInv i j) := by
  intro i k
  have hc0 : c ≠ 0 := ne_of_gt hc
  constructor
  · calc
      ∑ j, (c⁻¹ * gInv i j) *
          (scaleMetric (I := I) c hc g).inner x (basis j) (basis k)
          = ∑ j, gInv i j * g.inner x (basis j) (basis k) := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [scaleMetric_inner]
            field_simp [hc0]
      _ = if i = k then 1 else 0 := (hinv i k).1
  · calc
      ∑ j, (scaleMetric (I := I) c hc g).inner x (basis i) (basis j) *
          (c⁻¹ * gInv j k)
          = ∑ j, g.inner x (basis i) (basis j) * gInv j k := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [scaleMetric_inner]
            field_simp [hc0]
      _ = if i = k then 1 else 0 := (hinv i k).2

/-- A `(0,2)` squared norm scales by two inverse-metric factors under
`g ↦ c g`. -/
theorem normSq0S_two_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    normSq0S (I := I) (scaleMetric (I := I) c hc g) x 2 A =
      c⁻¹ * c⁻¹ * normSq0S (I := I) g x 2 A := by
  classical
  let basis : Module.Basis (RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    RicciFlower.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      RicciFlower.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      RicciFlower.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x basis gInv :=
    RicciFlower.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hinvScale :
      MetricInverseInBasis (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [normSq0S_two_eq_coord (I := I) (scaleMetric (I := I) c hc g) x basis
      (fun i j => c⁻¹ * gInv i j) hinvScale A,
    normSq0S_two_eq_coord (I := I) g x basis gInv hinv A]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  ring

end

end Tensor0SBundle
