import RicciFlower.GlobalGeometry.IndexForm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers sine test fields

This file is the geometric test-field/index-form layer for Myers.  It rewrites
the finite sum of sine test-field index forms into the trigonometric integral
consumed by `DiameterBound.lean`.

The curvature input is deliberately explicit.  The later Jacobi/curvature
producer should supply the actual curvature field and the Ricci trace identity;
this file only performs the algebraic finite-sum and integral bookkeeping.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Bundle Lecture07 intervalIntegral
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Myers sine coefficient `sin(pi t / L)`. -/
def sinCoeff (L : Real) (t : Real) : Real :=
  Real.sin (Real.pi / L * t)

/-- The Myers cosine coefficient `cos(pi t / L)`. -/
def cosCoeff (L : Real) (t : Real) : Real :=
  Real.cos (Real.pi / L * t)

/-- The sine test field `sin(pi t / L) E_i(t)` along a curve. -/
def sinField {ι : Type*} (L : Real) (gamma : Curve M)
    (Eframe : ι -> VectorFieldAlong I gamma) (i : ι) : VectorFieldAlong I gamma :=
  fun t => sinCoeff L t • Eframe i t

/-- The formal derivative of the sine test field when `E_i` is parallel. -/
def sinDerivField {ι : Type*} (L : Real) (gamma : Curve M)
    (Eframe : ι -> VectorFieldAlong I gamma) (i : ι) : VectorFieldAlong I gamma :=
  fun t => (Real.pi / L * cosCoeff L t) • Eframe i t

/-- Algebraic Myers index-form summation from pointwise norm and curvature-trace
identities.

The hypothesis `hL` is needed because the pointwise hypotheses are stated on
`Icc 0 L`; interval integrals over `0..L` use the unordered interval `[[0,L]]`
internally, which equals `Icc 0 L` only when `0 <= L`. -/
theorem sum_indexForm_eq_trig_integral_of_pointwise
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric I M) {gamma : Curve M}
    (V DV CurvV : ι -> VectorFieldAlong I gamma)
    {n : Nat} {L : Real} {r : Real -> Real}
    (hL : 0 <= L)
    (hcard : (Fintype.card ι : Real) = (n : Real) - 1)
    (hDV :
      forall i t, t ∈ Set.Icc (0 : Real) L ->
        g.inner (gamma t) (DV i t) (DV i t) =
          (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2)
    (hCurvSum :
      forall t, t ∈ Set.Icc (0 : Real) L ->
        (∑ i, g.inner (gamma t) (CurvV i t) (V i t)) =
          Real.sin (Real.pi / L * t) ^ 2 * r t)
    (hInt :
      forall i, IntervalIntegrable
        (fun t =>
          g.inner (gamma t) (DV i t) (DV i t) -
            g.inner (gamma t) (CurvV i t) (V i t))
        MeasureTheory.volume 0 L) :
    (∑ i, indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L)
      = ∫ t in (0 : Real)..L,
          ((n : Real) - 1) * (Real.pi / L) ^ 2 *
              Real.cos (Real.pi / L * t) ^ 2
            - Real.sin (Real.pi / L * t) ^ 2 * r t := by
  classical
  unfold indexForm
  rw [← intervalIntegral.integral_finset_sum
      (s := Finset.univ)
      (f := fun i t =>
        g.inner (gamma t) (DV i t) (DV i t) -
          g.inner (gamma t) (CurvV i t) (V i t))
      (h := by
        intro i _hi
        exact hInt i)]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : Real) L := by
    rwa [Set.uIcc_of_le hL] at ht
  calc
    (∑ i ∈ Finset.univ,
        (g.inner (gamma t) (DV i t) (DV i t) -
          g.inner (gamma t) (CurvV i t) (V i t)))
        = (∑ i, g.inner (gamma t) (DV i t) (DV i t)) -
            ∑ i, g.inner (gamma t) (CurvV i t) (V i t) := by
          simp [Finset.sum_sub_distrib]
    _ = (∑ _i : ι,
          (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2) -
          Real.sin (Real.pi / L * t) ^ 2 * r t := by
          rw [Finset.sum_congr rfl (fun i _hi => hDV i t htIcc),
            hCurvSum t htIcc]
    _ = ((n : Real) - 1) * (Real.pi / L) ^ 2 *
          Real.cos (Real.pi / L * t) ^ 2
        - Real.sin (Real.pi / L * t) ^ 2 * r t := by
          simp [Finset.sum_const, hcard, nsmul_eq_mul]
          ring

/-- Sine-field specialization of `sum_indexForm_eq_trig_integral_of_pointwise`.

`CurvE` is the unscaled curvature trace field, intended later to be
`R(E_i,T)T`.  The actual curvature input for the sine field is
`sin(pi t / L) * CurvE_i(t)`, so pairing it with
`sin(pi t / L) * E_i(t)` gives the expected `sin^2` factor. -/
theorem sum_indexForm_eq_trig_integral_of_sine_fields
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) {gamma : Curve M}
    (Eframe CurvE : ι -> VectorFieldAlong I gamma)
    {n : Nat} {L : Real} {r : Real -> Real}
    (hL : 0 <= L)
    (hcard : (Fintype.card ι : Real) = (n : Real) - 1)
    (hON :
      forall t, t ∈ Set.Icc (0 : Real) L -> forall i j,
        g.inner (gamma t) (Eframe i t) (Eframe j t) =
          if i = j then 1 else 0)
    (hCurv_trace :
      forall t, t ∈ Set.Icc (0 : Real) L ->
        (∑ i, g.inner (gamma t) (CurvE i t) (Eframe i t)) = r t)
    (hInt :
      forall i, IntervalIntegrable
        (fun t =>
          g.inner (gamma t)
              (sinDerivField (I := I) L gamma Eframe i t)
              (sinDerivField (I := I) L gamma Eframe i t) -
            g.inner (gamma t)
              (sinCoeff L t • CurvE i t)
              (sinField (I := I) L gamma Eframe i t))
        MeasureTheory.volume 0 L) :
    (∑ i, indexForm (I := I) g gamma
      (sinField (I := I) L gamma Eframe i)
      (sinDerivField (I := I) L gamma Eframe i)
      (fun t => sinCoeff L t • CurvE i t) 0 L)
      = ∫ t in (0 : Real)..L,
          ((n : Real) - 1) * (Real.pi / L) ^ 2 *
              Real.cos (Real.pi / L * t) ^ 2
            - Real.sin (Real.pi / L * t) ^ 2 * r t := by
  classical
  refine
    sum_indexForm_eq_trig_integral_of_pointwise
      (I := I) (g := g) (gamma := gamma)
      (V := fun i => sinField (I := I) L gamma Eframe i)
      (DV := fun i => sinDerivField (I := I) L gamma Eframe i)
      (CurvV := fun i => fun t => sinCoeff L t • CurvE i t)
      (n := n) (L := L) (r := r)
      hL hcard ?_ ?_ hInt
  · intro i t ht
    simp [sinDerivField, cosCoeff, hON t ht i i, pow_two, mul_assoc, mul_left_comm,
      mul_comm]
  · intro t ht
    have htrace := hCurv_trace t ht
    calc
      (∑ i,
          g.inner (gamma t) ((fun j => fun s => sinCoeff L s • CurvE j s) i t)
            ((fun j => sinField (I := I) L gamma Eframe j) i t))
          = (sinCoeff L t) ^ 2 *
              ∑ i, g.inner (gamma t) (CurvE i t) (Eframe i t) := by
            simp [sinField, pow_two, Finset.mul_sum, mul_assoc]
      _ = Real.sin (Real.pi / L * t) ^ 2 * r t := by
            rw [htrace]
            simp [sinCoeff]

end Myers
end GlobalGeometry
end RicciFlower
