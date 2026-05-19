import RicciFlower.Analysis.DivergenceTheorem.Gradient
import RicciFlower.LeviCivita.Smooth
import RicciFlower.LeviCivita.Uniqueness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Chart density and Levi-Civita Christoffel trace

This file contains the local coordinate bridge behind the identity
`partial_p log rho = Gamma^a_{p a}`.  The density-side matrix derivative lives
in `Analysis.DivergenceTheorem.Gradient`; this file supplies the
Levi-Civita/Christoffel trace side.
-/

namespace RicciFlower
namespace LeviCivita

open Bundle
open Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private lemma traceChristoffelAlg
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx → Idx → Real) (D : Idx → Idx → Idx → Real)
    (hsym : ∀ i j : Idx, gInv i j = gInv j i) (p : Idx) :
    (∑ a : Idx,
        (1 / 2 : Real) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
      =
    (1 / 2 : Real) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := by
  classical
  let S₁ : Real := ∑ a : Idx, ∑ l : Idx, gInv a l * D p a l
  let S₂ : Real := ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l
  let S₃ : Real := ∑ a : Idx, ∑ l : Idx, gInv a l * D l p a
  have hS₃ : S₃ = S₂ := by
    unfold S₂ S₃
    calc
      (∑ a : Idx, ∑ l : Idx, gInv a l * D l p a)
          = ∑ l : Idx, ∑ a : Idx, gInv a l * D l p a := by
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ a : Idx, gInv l a * D l p a := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hsym a l]
      _ = ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l := rfl
  have hsplit :
      (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        = S₁ + S₂ - S₃ := by
    unfold S₁ S₂ S₃
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc
    (∑ a : Idx,
        (1 / 2 : Real) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        =
      (1 / 2 : Real) *
        (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a)) := by
          rw [Finset.mul_sum]
    _ = (1 / 2 : Real) * (S₁ + S₂ - S₃) := by
          rw [hsplit]
    _ = (1 / 2 : Real) * S₁ := by
          rw [hS₃]
          ring
    _ = (1 / 2 : Real) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := rfl

/-- Trace of the Levi-Civita Christoffel formula in a point-centered coordinate
frame.

Mathematically this is
`sum_a Gamma^a_{p a} = (1/2) sum_{i,j} g^{ij} partial_p g_{ij}`.
The right-hand side is stated with intrinsic coordinate-frame directional
derivatives, so it is independent of the chart-density implementation. -/
theorem lcTrace_halfTrace
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (hinv : MetricInverseInBasis (I := I) g x
      (coordinateFrameAt_toBasis (I := I) x) gInv)
    (hsym :
      ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = gInv j i)
    (p : CoordinateIdx (𝕜 := Real) E) :
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
      =
    (1 / 2 : Real) *
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInv i j *
            directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
              (fun y : M =>
                g.inner y (coordinateFrameAt (I := I) x i y)
                  (coordinateFrameAt (I := I) x j y)) x := by
  classical
  let D :
      CoordinateIdx (𝕜 := Real) E →
        CoordinateIdx (𝕜 := Real) E →
          CoordinateIdx (𝕜 := Real) E → Real :=
    fun r i j =>
      directionalDeriv (I := I) (coordinateFrameAt (I := I) x r)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x i y)
            (coordinateFrameAt (I := I) x j y)) x
  have hformula :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        christoffelSymbolInFrame cov
          (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a =
        (1 / 2 : Real) *
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv a l * (D p a l + D a p l - D l p a) := by
    intro a
    simpa [D, coordinateFrameAt_toBasis] using
      coordinateFrame_christoffel_formula_point_of_isLeviCivita
        (I := I) (cov := cov) g hLC x
        (coordinateFrameAt_mem (I := I) x) gInv hinv p a a
  calc
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
        =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        (1 / 2 : Real) *
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv a l * (D p a l + D a p l - D l p a) := by
          refine Finset.sum_congr rfl fun a _ => hformula a
    _ =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E, gInv i j * D p i j := by
          exact traceChristoffelAlg gInv D hsym p
    _ =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j *
              directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x i y)
                    (coordinateFrameAt (I := I) x j y)) x := rfl

/-- Model-coordinate form of `lcTrace_halfTrace`, using the fixed-chart inverse
metric components and derivatives of fixed-chart metric coefficients. -/
theorem lcTrace_halfTrace_model
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
      =
    (1 / 2 : Real) *
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            fderivWithin Real
              (metricFlatModelInChart_component (I := I) g x i j)
              (Set.range I) (extChartAt I x x) ((Module.finBasis Real E) p) := by
  classical
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      inverseMetricFlatModelInChart_component (I := I) g x i j
        (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x
      (coordinateFrameAt_toBasis (I := I) x) gInv := by
    simpa [gInv] using
      inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  have hsym :
      ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = gInv j i := by
    intro i j
    exact inverseMetricFlatModelInChart_component_center_eq_symm
      (I := I) g x i j
  calc
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
        =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            gInv i j *
              directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x i y)
                    (coordinateFrameAt (I := I) x j y)) x := by
          exact lcTrace_halfTrace (I := I) (cov := cov) g hLC x gInv hinv hsym p
    _ =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              fderivWithin Real
                (metricFlatModelInChart_component (I := I) g x i j)
                (Set.range I) (extChartAt I x x) ((Module.finBasis Real E) p) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp [gInv]
          rw [← metricFlatModelInChart_component_deriv_center
            (I := I) g x p i j]
          simp [extChartAt]

/-- On the fixed coordinate domain, the volume-layer chart Gram matrix is the
metric coefficient of the coordinate frame. -/
private theorem chartGram_eq_metricComp_of_mem
    (g : SmoothRiemannianMetric I M) (x : M)
    {y : M} (hy : y ∈ coordinateFrameSet (I := I) x)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x y i j =
      g.inner y (coordinateFrameAt (I := I) x i y)
        (coordinateFrameAt (I := I) x j y) := by
  have hybase :
      y ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy
  have hi :
      RicciFlower.Analysis.Volume.chartBasisVecFiber (I := I) x i y =
        coordinateFrameAt (I := I) x i y := by
    change
      (trivializationAt E (TangentSpace I : M → Type _) x).symm y
          ((Module.finBasis Real E) i) =
        (trivializationAt E (TangentSpace I : M → Type _) x).localFrame
          (Module.finBasis Real E) i y
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := trivializationAt E (TangentSpace I : M → Type _) x)
      (b := Module.finBasis Real E) (i := i) hybase]
    simp [Bundle.Trivialization.basisAt]
  have hj :
      RicciFlower.Analysis.Volume.chartBasisVecFiber (I := I) x j y =
        coordinateFrameAt (I := I) x j y := by
    change
      (trivializationAt E (TangentSpace I : M → Type _) x).symm y
          ((Module.finBasis Real E) j) =
        (trivializationAt E (TangentSpace I : M → Type _) x).localFrame
          (Module.finBasis Real E) j y
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := trivializationAt E (TangentSpace I : M → Type _) x)
      (b := Module.finBasis Real E) (i := j) hybase]
    simp [Bundle.Trivialization.basisAt]
  simp [RicciFlower.Analysis.Volume.chartGramMatrix, hi, hj]

/-- At the chart center, the volume-layer Gram matrix agrees with the
Levi-Civita fixed-chart metric coefficient. -/
private theorem chartGram_eq_metricFlat_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x x i j =
      metricFlatModelInChart_component (I := I) g x i j (extChartAt I x x) := by
  rw [metricFlatModelInChart_component_center]
  rw [chartGram_eq_metricComp_of_mem (I := I) g x
    (coordinateFrameAt_mem (I := I) x) i j]

/-- The inverse Gram matrix used by the volume density is the inverse metric in
the point-centered coordinate-frame basis. -/
private theorem chartInvGram_metricInverse_center
    (g : SmoothRiemannianMetric I M) (x : M) :
    MetricInverseInBasis (I := I) g x
      (coordinateFrameAt_toBasis (I := I) x)
      (fun i j : CoordinateIdx (𝕜 := Real) E =>
        RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
          (I := I) g x x i j) := by
  classical
  have hxbase :
      x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  have hmetric :
      ∀ k j : CoordinateIdx (𝕜 := Real) E,
        g.inner x ((coordinateFrameAt_toBasis (I := I) x) k)
            ((coordinateFrameAt_toBasis (I := I) x) j) =
          RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x x k j := by
    intro k j
    simpa [coordinateFrameAt_toBasis] using
      (chartGram_eq_metricComp_of_mem (I := I) g x
        (coordinateFrameAt_mem (I := I) x) k j).symm
  intro i j
  constructor
  · have hmat :=
      RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix
        (I := I) g x hxbase
    have hentry := congrArg (fun A =>
      A i j) hmat
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
            (I := I) g x x i k *
          g.inner x ((coordinateFrameAt_toBasis (I := I) x) k)
            ((coordinateFrameAt_toBasis (I := I) x) j))
          =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
              (I := I) g x x i k *
            RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x x k j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hmetric k j]
      _ = (if i = j then 1 else 0) := by
            simpa [Matrix.mul_apply] using hentry
  · have hmat :=
      RicciFlower.Analysis.DivergenceTheorem.chartGramMatrix_mul_chartInvGramMatrix
        (I := I) g x hxbase
    have hentry := congrArg (fun A =>
      A i j) hmat
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        g.inner x ((coordinateFrameAt_toBasis (I := I) x) i)
            ((coordinateFrameAt_toBasis (I := I) x) k) *
          RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
            (I := I) g x x k j)
          =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x x i k *
            RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
              (I := I) g x x k j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hmetric i k]
      _ = (if i = j then 1 else 0) := by
            simpa [Matrix.mul_apply] using hentry

/-- Christoffel trace in terms of the volume-layer inverse Gram matrix and
coordinate-frame directional derivatives. -/
theorem lcTrace_halfTrace_chart
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
      =
    (1 / 2 : Real) *
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
              (I := I) g x x i j *
            directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
              (fun y : M =>
                g.inner y (coordinateFrameAt (I := I) x i y)
                  (coordinateFrameAt (I := I) x j y)) x := by
  classical
  exact lcTrace_halfTrace (I := I) (cov := cov) g hLC x
    (fun i j : CoordinateIdx (𝕜 := Real) E =>
      RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
        (I := I) g x x i j)
    (chartInvGram_metricInverse_center (I := I) g x)
    (fun i j =>
      (RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix_symm
        (I := I) g x x i j).symm)
    p

/-- Near the chart center, the volume-layer Gram coefficient pulled back to the
model chart agrees with the Levi-Civita fixed-chart metric coefficient. -/
private theorem chartGram_eq_metricFlat_eventually
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (fun y : E =>
      RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
        ((extChartAt I x).symm y) i j)
      =ᶠ[nhds (extChartAt I x x)]
    metricFlatModelInChart_component (I := I) g x i j := by
  filter_upwards [extChartAt_target_mem_nhds' (I := I)
      (x := x) (y := extChartAt I x x) (by simp)] with y hy
  let m : M := (extChartAt I x).symm y
  have hm_source : m ∈ (extChartAt I x).source := by
    exact (extChartAt I x).map_target hy
  have hm_coord : m ∈ coordinateFrameSet (I := I) x := by
    simpa [m, coordinateFrameSet, coordinateTrivializationAt, extChartAt_source]
      using hm_source
  have hy_eq : extChartAt I x m = y := by
    exact (extChartAt I x).right_inv hy
  calc
    RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
        ((extChartAt I x).symm y) i j
        = g.inner m (coordinateFrameAt (I := I) x i m)
            (coordinateFrameAt (I := I) x j m) := by
          simpa [m] using chartGram_eq_metricComp_of_mem (I := I) g x hm_coord i j
    _ = metricFlatModelInChart_component (I := I) g x i j (extChartAt I x m) := by
          exact (metricFlatModelInChart_component_of_mem
            (I := I) g x hm_coord i j).symm
    _ = metricFlatModelInChart_component (I := I) g x i j y := by
          rw [hy_eq]

/-- The partial derivative of the volume-layer Gram coefficient equals the
fixed-chart metric-component derivative at the chart center. -/
private theorem chartGram_partial_eq_metricFlat_deriv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p i j : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
            ((extChartAt I x).symm y) i j)
        (extChartAt I x x)
      =
    fderivWithin Real
      (metricFlatModelInChart_component (I := I) g x i j)
      (Set.range I) (extChartAt I x x) ((Module.finBasis Real E) p) := by
  unfold RicciFlower.Analysis.DivergenceTheorem.partialDeriv
  have heq := chartGram_eq_metricFlat_eventually (I := I) g x i j
  have hf :
      fderiv Real
        (fun y : E =>
          RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
            ((extChartAt I x).symm y) i j) (extChartAt I x x) =
      fderiv Real (metricFlatModelInChart_component (I := I) g x i j)
        (extChartAt I x x) := by
    exact Filter.EventuallyEq.fderiv_eq heq
  have hxbase :
      fderivWithin Real (metricFlatModelInChart_component (I := I) g x i j)
        (Set.range I) (extChartAt I x x) =
      fderiv Real (metricFlatModelInChart_component (I := I) g x i j)
        (extChartAt I x x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    simp
  rw [hf, hxbase]

private theorem chartGram_partial_eq_directional
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p i j : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (fun y : E =>
          RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
            ((extChartAt I x).symm y) i j)
        (extChartAt I x x)
      =
    directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
      (fun y : M =>
        g.inner y (coordinateFrameAt (I := I) x i y)
          (coordinateFrameAt (I := I) x j y)) x := by
  rw [chartGram_partial_eq_metricFlat_deriv (I := I) g x p i j]
  exact metricFlatModelInChart_component_deriv_center (I := I) g x p i j

/-- Christoffel trace in the exact matrix-trace form produced by the
chart-density derivative theorem. -/
theorem lcTrace_halfTrace_density
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
      =
    (1 / 2 : Real) *
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
              (I := I) g x x i j *
            RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
              (fun y : E =>
                RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
                  ((extChartAt I x).symm y) i j)
              (extChartAt I x x) := by
  classical
  calc
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)
        =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
                (I := I) g x x i j *
              directionalDeriv (I := I) (coordinateFrameAt (I := I) x p)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x i y)
                    (coordinateFrameAt (I := I) x j y)) x := by
          exact lcTrace_halfTrace_chart (I := I) (cov := cov) g hLC x p
    _ =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
                (I := I) g x x i j *
              RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
                (fun y : E =>
                  RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
                    ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [chartGram_partial_eq_directional (I := I) g x p i j]

/-- Point-centered density/Christoffel trace identity:
`partial_p log rho = Gamma^a_{p a}`. -/
theorem lcTrace_logDensity
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
          (I := I) g x) (extChartAt I x x) /
      RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
      =
    ∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a := by
  have hρ :
      RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
          (I := I) g x (extChartAt I x x) =
        RicciFlower.Analysis.Volume.chartDensity (I := I) g x x := by
    change RicciFlower.Analysis.Volume.chartDensity (I := I) g x
        ((extChartAt I x).symm (extChartAt I x x)) =
      RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  calc
    RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
          (I := I) g x) (extChartAt I x x) /
      RicciFlower.Analysis.Volume.chartDensity (I := I) g x x
        =
      RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
        (RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
          (I := I) g x) (extChartAt I x x) /
      RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE
          (I := I) g x (extChartAt I x x) := by
          rw [hρ]
    _ =
      (1 / 2 : Real) *
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            RicciFlower.Analysis.DivergenceTheorem.chartInvGramMatrix
                (I := I) g x x i j *
              RicciFlower.Analysis.DivergenceTheorem.partialDeriv (E := E) p
                (fun y : E =>
                  RicciFlower.Analysis.Volume.chartGramMatrix (I := I) g x
                    ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
          exact
            RicciFlower.Analysis.DivergenceTheorem.chartDensityOnE_partial_div_eq_half_trace_invGram_partialGram
              (I := I) g x p
    _ =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelSymbolInFrame cov
          (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a := by
          exact (lcTrace_halfTrace_density
            (I := I) (cov := cov) g hLC x p).symm

end LeviCivita
end RicciFlower
