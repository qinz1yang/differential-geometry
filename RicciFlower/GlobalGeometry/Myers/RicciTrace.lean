import RicciFlower.GlobalGeometry.Myers.TestFields
import RicciFlower.GlobalGeometry.Myers.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers Ricci-trace assembly

This file connects the sine test-field index sum to the abstract Ricci lower
bound used by the Myers diameter estimate.

The actual identity between a curvature trace and the abstract Ricci tensor is
not proved here.  It is recorded as `hTrace`, because `Ric` is a
`Curvature.Tensor02Section` and is not definitionally tied to a concrete
Riemann curvature operator.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Bundle Lecture07 intervalIntegral
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Producer P4 (finishing): assemble the M1-ready index-sum data
`(hr_cont, hr, hsum_eq)` from a parallel orthonormal frame `Eframe ⟂ T`, the
pointwise Ricci lower bound, and the unit-speed condition.

The single remaining honest geometric input is `hTrace`, the Ricci-trace
realization `∑_i <CurvE_i, E_i> = Ric(T,T)` (with `CurvE_i` intended to be the
curvature field `R(E_i,T)T`).  The abstract `Ric : Tensor02Section` is not
definitionally the trace of a curvature operator, so this identity is supplied
as a hypothesis to be discharged later by the curvature producer.  Everything
else is proved here. -/
theorem myers_index_sum_data
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (Ric : Curvature.Tensor02Section (I := I) (M := M))
    {gamma : Curve M}
    (Eframe CurvE : ι -> VectorFieldAlong I gamma)
    {n : Nat} {k L : Real} (r : Real -> Real)
    (hn : 1 < n)
    (hL : 0 <= L)
    (hcard : (Fintype.card ι : Real) = (n : Real) - 1)
    (hr_def : forall t, r t =
      Ric (gamma t)
        (Curvature.vec2 (I := I) (velocityAlong I gamma t) (velocityAlong I gamma t)))
    (hRic : RicciLowerBound (I := I) (M := M) g Ric (((n - 1 : Nat) : Real) * k))
    (hON : forall t, t ∈ Set.Icc (0 : Real) L -> forall i j,
      g.inner (gamma t) (Eframe i t) (Eframe j t) = if i = j then 1 else 0)
    (hunit : forall t, t ∈ Set.Icc (0 : Real) L ->
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1)
    (hTrace : forall t, t ∈ Set.Icc (0 : Real) L ->
      (∑ i, g.inner (gamma t) (CurvE i t) (Eframe i t)) = r t)
    (hr_cont : ContinuousOn r (Set.Icc (0 : Real) L))
    (hInt : forall i, IntervalIntegrable
      (fun t =>
        g.inner (gamma t)
            (sinDerivField (I := I) L gamma Eframe i t)
            (sinDerivField (I := I) L gamma Eframe i t)
          - g.inner (gamma t)
            (sinCoeff L t • CurvE i t)
            (sinField (I := I) L gamma Eframe i t))
      MeasureTheory.volume 0 L) :
    ContinuousOn r (Set.Icc (0 : Real) L)
      ∧ (forall t, t ∈ Set.Icc (0 : Real) L -> ((n : Real) - 1) * k <= r t)
      ∧ (∑ i, indexForm (I := I) g gamma
          (sinField (I := I) L gamma Eframe i)
          (sinDerivField (I := I) L gamma Eframe i)
          (fun t => sinCoeff L t • CurvE i t) 0 L)
        = ∫ t in (0 : Real)..L,
            ((n : Real) - 1) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2
              - Real.sin (Real.pi / L * t) ^ 2 * r t := by
  refine ⟨hr_cont, ?_, ?_⟩
  · intro t ht
    have hcast : (((n - 1 : Nat) : Real)) = (n : Real) - 1 := by
      rw [Nat.cast_sub hn.le, Nat.cast_one]
    have h := hRic (gamma t) (velocityAlong I gamma t)
    rw [hunit t ht, mul_one, ← hr_def t] at h
    rwa [hcast] at h
  · exact
      sum_indexForm_eq_trig_integral_of_sine_fields
        (I := I) (g := g) (gamma := gamma)
        Eframe CurvE (n := n) (L := L) (r := r)
        hL hcard hON hTrace hInt

end Myers
end GlobalGeometry
end RicciFlower
