import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Variation.RicciIntegral
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Interval Manifold Topology

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private def endpointExponentialWeight (L t : Real) : Real :=
  (1 - Real.exp (-2 * t)) * (1 - Real.exp (-2 * (L - t)))

private def endpointExponentialWeightDeriv (L t : Real) : Real :=
  2 * (Real.exp (-2 * t) - Real.exp (-2 * (L - t)))

private theorem endpointExponentialWeight_hasDerivAt (L t : Real) :
    HasDerivAt (endpointExponentialWeight L)
      (endpointExponentialWeightDeriv L t) t := by
  unfold endpointExponentialWeight endpointExponentialWeightDeriv
  have ha : HasDerivAt (fun s : Real => 1 - Real.exp (-2 * s))
      (2 * Real.exp (-2 * t)) t := by
    have hraw :=
      (hasDerivAt_const t (1 : Real)).sub
        (((hasDerivAt_id t).const_mul (-2)).exp)
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [Pi.sub_apply, id_eq]
    · simp only [id_eq]
      ring
  have hb : HasDerivAt (fun s : Real => 1 - Real.exp (-2 * (L - s)))
      (-2 * Real.exp (-2 * (L - t))) t := by
    have hinner : HasDerivAt (fun s : Real => -2 * (L - s)) 2 t := by
      have hraw := ((hasDerivAt_const t L).sub (hasDerivAt_id t)).const_mul (-2)
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · simp only [Pi.sub_apply, id_eq]
      · norm_num
    have hraw := (hasDerivAt_const t (1 : Real)).sub hinner.exp
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [Pi.sub_apply]
    · ring
  have hmul := ha.mul hb
  refine (hmul.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply]
  · ring

private theorem endpointExponentialWeight_deriv (L t : Real) :
    deriv (endpointExponentialWeight L) t =
      endpointExponentialWeightDeriv L t :=
  (endpointExponentialWeight_hasDerivAt L t).deriv

@[simp] private theorem endpointExponentialWeight_zero (L : Real) :
    endpointExponentialWeight L 0 = 0 := by
  simp [endpointExponentialWeight]

@[simp] private theorem endpointExponentialWeight_self (L : Real) :
    endpointExponentialWeight L L = 0 := by
  simp [endpointExponentialWeight]

private theorem endpointExponentialWeight_mem_Icc {L t : Real}
    (ht : t ∈ Set.Icc (0 : Real) L) :
    endpointExponentialWeight L t ∈ Set.Icc (0 : Real) 1 := by
  have ha : Real.exp (-2 * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [ht.1])
  have hb : Real.exp (-2 * (L - t)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [ht.2])
  have hA : 1 - Real.exp (-2 * t) ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · linarith
    · linarith [Real.exp_pos (-2 * t)]
  have hB : 1 - Real.exp (-2 * (L - t)) ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · linarith
    · linarith [Real.exp_pos (-2 * (L - t))]
  unfold endpointExponentialWeight
  exact ⟨mul_nonneg hA.1 hB.1,
    (mul_le_mul hA.2 hB.2 hB.1 (by norm_num)).trans_eq (by norm_num)⟩

private theorem endpointExponentialWeightDeriv_nonneg {L t : Real}
    (htm : t ≤ L / 2) :
    0 ≤ endpointExponentialWeightDeriv L t := by
  unfold endpointExponentialWeightDeriv
  have hle : Real.exp (-2 * (L - t)) ≤ Real.exp (-2 * t) := by
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

private theorem endpointExponentialWeightDeriv_nonpos {L t : Real}
    (htm : L / 2 ≤ t) :
    endpointExponentialWeightDeriv L t ≤ 0 := by
  unfold endpointExponentialWeightDeriv
  have hle : Real.exp (-2 * t) ≤ Real.exp (-2 * (L - t)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

private theorem endpointExponentialWeightDeriv_sq_eq (L t : Real) :
    endpointExponentialWeightDeriv L t ^ 2 =
      4 * (Real.exp (-4 * t) + Real.exp (-4 * (L - t)) -
        2 * Real.exp (-2 * L)) := by
  unfold endpointExponentialWeightDeriv
  have ha : Real.exp (-2 * t) * Real.exp (-2 * t) = Real.exp (-4 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (-2 * (L - t)) * Real.exp (-2 * (L - t)) =
      Real.exp (-4 * (L - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hab : Real.exp (-2 * t) * Real.exp (-2 * (L - t)) =
      Real.exp (-2 * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [sq]
  nlinarith

private theorem endpointExponentialWeightDeriv_sq_integral (L : Real) :
    (∫ t in (0 : Real)..L, endpointExponentialWeightDeriv L t ^ 2) =
      2 * (1 - Real.exp (-4 * L)) - 8 * L * Real.exp (-2 * L) := by
  simp_rw [endpointExponentialWeightDeriv_sq_eq]
  have hfirst :
      (∫ t in (0 : Real)..L, Real.exp (-4 * t)) =
        (1 - Real.exp (-4 * L)) / 4 := by
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => -(1 / 4 : Real) * Real.exp (-4 * s))
          (Real.exp (-4 * t)) t := by
      have hraw :=
        (((hasDerivAt_id t).const_mul (-4)).exp).const_mul
          (-(1 / 4 : Real))
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · simp only [id_eq]
      · simp only [id_eq]
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-4 * t))).intervalIntegrable 0 L)]
    simp
    ring
  have hsecond :
      (∫ t in (0 : Real)..L, Real.exp (-4 * (L - t))) =
        (1 - Real.exp (-4 * L)) / 4 := by
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => (1 / 4 : Real) * Real.exp (-4 * (L - s)))
          (Real.exp (-4 * (L - t))) t := by
      have hinner : HasDerivAt (fun s : Real => -4 * (L - s)) 4 t := by
        have hraw := ((hasDerivAt_const t L).sub (hasDerivAt_id t)).const_mul (-4)
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
        · simp only [Pi.sub_apply, id_eq]
        · norm_num
      have hraw := hinner.exp.const_mul (1 / 4 : Real)
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · rfl
      · ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-4 * (L - t)))).intervalIntegrable 0 L)]
    simp
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_add, hfirst, hsecond,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [sub_zero, smul_eq_mul]
      ring
    · exact (by fun_prop : Continuous
        (fun x : Real => Real.exp (-4 * x))).intervalIntegrable 0 L
    · exact (by fun_prop : Continuous
        (fun x : Real => Real.exp (-4 * (L - x)))).intervalIntegrable 0 L
  · exact (by fun_prop : Continuous
      (fun x : Real => Real.exp (-4 * x) +
        Real.exp (-4 * (L - x)))).intervalIntegrable 0 L
  · exact (by fun_prop : Continuous
      (fun _x : Real => 2 * Real.exp (-2 * L))).intervalIntegrable 0 L

private theorem endpointExponentialWeightDeriv_sq_integral_le
    {L : Real} (hL : 0 ≤ L) :
    (∫ t in (0 : Real)..L, endpointExponentialWeightDeriv L t ^ 2) ≤ 2 := by
  rw [endpointExponentialWeightDeriv_sq_integral L]
  have hExp : 0 < Real.exp (-4 * L) := Real.exp_pos _
  have hterm : 0 ≤ 8 * L * Real.exp (-2 * L) := by positivity
  linarith

private theorem endpointExponentialWeight_sq_deficit_integral_le
    {L : Real} (hL : 0 ≤ L) :
    (∫ t in (0 : Real)..L, 1 - endpointExponentialWeight L t ^ 2) ≤
      3 / 2 := by
  have hpoint (t : Real) (ht : t ∈ Set.Icc (0 : Real) L) :
      1 - endpointExponentialWeight L t ^ 2 ≤
        2 * Real.exp (-2 * t) + 2 * Real.exp (-2 * (L - t)) -
          Real.exp (-2 * t) ^ 2 - Real.exp (-2 * (L - t)) ^ 2 := by
    have hA : Real.exp (-2 * t) ∈ Set.Icc (0 : Real) 1 := by
      constructor
      · exact (Real.exp_pos _).le
      · rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith [ht.1])
    have hB : Real.exp (-2 * (L - t)) ∈ Set.Icc (0 : Real) 1 := by
      constructor
      · exact (Real.exp_pos _).le
      · rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith [ht.2])
    unfold endpointExponentialWeight
    have hlinear : 0 ≤ 4 - 2 * Real.exp (-2 * t) -
        2 * Real.exp (-2 * (L - t)) := by
      linarith [hA.2, hB.2]
    have hfactor : 0 ≤ 4 + Real.exp (-2 * t) * Real.exp (-2 * (L - t)) -
        2 * Real.exp (-2 * t) - 2 * Real.exp (-2 * (L - t)) := by
      nlinarith [mul_nonneg hA.1 hB.1]
    nlinarith [mul_nonneg (mul_nonneg hA.1 hB.1) hfactor]
  have hleft : IntervalIntegrable
      (fun t : Real => 1 - endpointExponentialWeight L t ^ 2) volume 0 L :=
    (by
      unfold endpointExponentialWeight
      fun_prop : Continuous
        (fun t : Real => 1 - endpointExponentialWeight L t ^ 2)).intervalIntegrable 0 L
  have hright : IntervalIntegrable
      (fun t : Real =>
        2 * Real.exp (-2 * t) + 2 * Real.exp (-2 * (L - t)) -
          Real.exp (-2 * t) ^ 2 - Real.exp (-2 * (L - t)) ^ 2) volume 0 L :=
    (by fun_prop : Continuous
      (fun t : Real =>
        2 * Real.exp (-2 * t) + 2 * Real.exp (-2 * (L - t)) -
          Real.exp (-2 * t) ^ 2 - Real.exp (-2 * (L - t)) ^ 2)).intervalIntegrable 0 L
  have hmono := intervalIntegral.integral_mono_on hL hleft hright hpoint
  have hA : (∫ t in (0 : Real)..L, Real.exp (-2 * t)) =
      (1 - Real.exp (-2 * L)) / 2 := by
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => -(1 / 2 : Real) * Real.exp (-2 * s))
          (Real.exp (-2 * t)) t := by
      have hraw :=
        (((hasDerivAt_id t).const_mul (-2)).exp).const_mul
          (-(1 / 2 : Real))
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp only [id_eq])).congr_deriv ?_
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-2 * t))).intervalIntegrable 0 L)]
    simp
    ring
  have hB : (∫ t in (0 : Real)..L, Real.exp (-2 * (L - t))) =
      (1 - Real.exp (-2 * L)) / 2 := by
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => (1 / 2 : Real) * Real.exp (-2 * (L - s)))
          (Real.exp (-2 * (L - t))) t := by
      have hinner : HasDerivAt (fun s : Real => -2 * (L - s)) 2 t := by
        have hraw := ((hasDerivAt_const t L).sub (hasDerivAt_id t)).const_mul (-2)
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => by
            simp only [Pi.sub_apply, id_eq])).congr_deriv ?_
        norm_num
      have hraw := hinner.exp.const_mul (1 / 2 : Real)
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _s => rfl)).congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-2 * (L - t)))).intervalIntegrable 0 L)]
    simp
    ring
  have hA2 : (∫ t in (0 : Real)..L, Real.exp (-2 * t) ^ 2) =
      (1 - Real.exp (-4 * L)) / 4 := by
    have heq (t : Real) : Real.exp (-2 * t) ^ 2 = Real.exp (-4 * t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    simp_rw [heq]
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => -(1 / 4 : Real) * Real.exp (-4 * s))
          (Real.exp (-4 * t)) t := by
      have hraw :=
        (((hasDerivAt_id t).const_mul (-4)).exp).const_mul
          (-(1 / 4 : Real))
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp only [id_eq])).congr_deriv ?_
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-4 * t))).intervalIntegrable 0 L)]
    simp
    ring
  have hB2 : (∫ t in (0 : Real)..L, Real.exp (-2 * (L - t)) ^ 2) =
      (1 - Real.exp (-4 * L)) / 4 := by
    have heq (t : Real) : Real.exp (-2 * (L - t)) ^ 2 =
        Real.exp (-4 * (L - t)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    simp_rw [heq]
    have hanti (t : Real) :
        HasDerivAt (fun s : Real => (1 / 4 : Real) * Real.exp (-4 * (L - s)))
          (Real.exp (-4 * (L - t))) t := by
      have hinner : HasDerivAt (fun s : Real => -4 * (L - s)) 4 t := by
        have hraw := ((hasDerivAt_const t L).sub (hasDerivAt_id t)).const_mul (-4)
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => by
            simp only [Pi.sub_apply, id_eq])).congr_deriv ?_
        norm_num
      have hraw := hinner.exp.const_mul (1 / 4 : Real)
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _s => rfl)).congr_deriv ?_
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t)
      ((by fun_prop : Continuous
        (fun t : Real => Real.exp (-4 * (L - t)))).intervalIntegrable 0 L)]
    simp
    ring
  calc
    (∫ t in (0 : Real)..L, 1 - endpointExponentialWeight L t ^ 2) ≤
        ∫ t in (0 : Real)..L,
          2 * Real.exp (-2 * t) + 2 * Real.exp (-2 * (L - t)) -
            Real.exp (-2 * t) ^ 2 - Real.exp (-2 * (L - t)) ^ 2 := hmono
    _ = 3 / 2 - 2 * Real.exp (-2 * L) + Real.exp (-4 * L) / 2 := by
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hA, hB, hA2, hB2]
      · ring
      all_goals exact (by fun_prop : Continuous _).intervalIntegrable 0 L
    _ ≤ 3 / 2 := by
      have hc : Real.exp (-4 * L) = Real.exp (-2 * L) ^ 2 := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [hc]
      have hce : Real.exp (-2 * L) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.exp_pos (-2 * L)]

private theorem integral_two_weight_mul_deriv (L a b : Real) :
    (∫ t in a..b, 2 * endpointExponentialWeight L t *
      endpointExponentialWeightDeriv L t) =
        endpointExponentialWeight L b ^ 2 -
          endpointExponentialWeight L a ^ 2 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => endpointExponentialWeight L s ^ 2)
    (fun t _ => by
      have hraw := (endpointExponentialWeight_hasDerivAt L t).pow 2
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · simp only [Pi.pow_apply]
      · ring)
    ((by
      unfold endpointExponentialWeight endpointExponentialWeightDeriv
      fun_prop : Continuous
        (fun t : Real => 2 * endpointExponentialWeight L t *
          endpointExponentialWeightDeriv L t)).intervalIntegrable a b)

private theorem integral_two_mul_mul_exp_neg_two (a b : Real) :
    (∫ t in a..b, 2 * t * Real.exp (-2 * t)) =
      -(b + 1 / 2) * Real.exp (-2 * b) -
        (-(a + 1 / 2) * Real.exp (-2 * a)) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => -(s + 1 / 2) * Real.exp (-2 * s))
    (fun t _ => by
      have hlin : HasDerivAt (fun s : Real => -(s + 1 / 2)) (-1) t := by
        have hraw := ((hasDerivAt_id t).add_const (1 / 2)).neg
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
        · rfl
        · norm_num
      have hexp : HasDerivAt (fun s : Real => Real.exp (-2 * s))
          (-2 * Real.exp (-2 * t)) t := by
        have hraw := ((hasDerivAt_id t).const_mul (-2)).exp
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
        · simp only [id_eq]
        · simp only [id_eq]
          ring
      have hraw := hlin.mul hexp
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · rfl
      · ring)
    ((by fun_prop : Continuous
      (fun t : Real => 2 * t * Real.exp (-2 * t))).intervalIntegrable a b)

private theorem integral_two_mul_reverse_mul_exp_neg_two (L a b : Real) :
    (∫ t in a..b, 2 * (L - t) * Real.exp (-2 * (L - t))) =
      (L - b + 1 / 2) * Real.exp (-2 * (L - b)) -
        (L - a + 1 / 2) * Real.exp (-2 * (L - a)) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => (L - s + 1 / 2) * Real.exp (-2 * (L - s)))
    (fun t _ => by
      have hlin : HasDerivAt (fun s : Real => L - s + 1 / 2) (-1) t := by
        have hraw :=
          ((hasDerivAt_const t L).sub (hasDerivAt_id t)).add_const (1 / 2)
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
        · simp only [Pi.sub_apply, id_eq]
        · norm_num
      have hinner : HasDerivAt (fun s : Real => -2 * (L - s)) 2 t := by
        have hraw := ((hasDerivAt_const t L).sub (hasDerivAt_id t)).const_mul
          (-2)
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
        · simp only [Pi.sub_apply, id_eq]
        · norm_num
      have hexp : HasDerivAt (fun s : Real => Real.exp (-2 * (L - s)))
          (2 * Real.exp (-2 * (L - t))) t := by
        have hraw := hinner.exp
        refine (hraw.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _s => rfl)).congr_deriv ?_
        ring
      have hraw := hlin.mul hexp
      refine (hraw.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · rfl
      · ring)
    ((by fun_prop : Continuous
      (fun t : Real => 2 * (L - t) *
        Real.exp (-2 * (L - t)))).intervalIntegrable a b)

private theorem endpointExponentialWeight_second_deriv_integral_le
    {L : Real} (hL : 0 ≤ L) (u : Real → Real)
    (hu : ContDiff Real 2 u)
    (hderiv_le : ∀ t ∈ Set.Icc (0 : Real) L,
      |deriv u t| ≤ Real.sqrt (u t))
    (hsqrt_left : ∀ t ∈ Set.Icc (0 : Real) (L / 2),
      Real.sqrt (u t) ≤ Real.sqrt (u 0) + t / 2)
    (hsqrt_right : ∀ t ∈ Set.Icc (L / 2) L,
      Real.sqrt (u t) ≤ Real.sqrt (u L) + (L - t) / 2) :
    (∫ t in (0 : Real)..L, endpointExponentialWeight L t ^ 2 *
      deriv (deriv u) t) ≤ Real.sqrt (u 0) + Real.sqrt (u L) + 1 := by
  let w : Real → Real := endpointExponentialWeight L
  let dw : Real → Real := endpointExponentialWeightDeriv L
  let q : Real → Real := fun t => -(2 * w t * dw t) * deriv u t
  have hw_deriv (t : Real) : HasDerivAt w (dw t) t := by
    exact endpointExponentialWeight_hasDerivAt L t
  have hw_cont : Continuous w :=
    continuous_iff_continuousAt.mpr fun t => (hw_deriv t).continuousAt
  have hdw_cont : Continuous dw := by
    change Continuous (fun t : Real =>
      2 * (Real.exp (-2 * t) - Real.exp (-2 * (L - t))))
    fun_prop
  have hdu_cont : Continuous (deriv u) :=
    hu.continuous_deriv (by norm_num)
  have hw2_deriv (t : Real) :
      HasDerivAt (fun s => w s ^ 2) (2 * w t * dw t) t := by
    have hraw := (hw_deriv t).pow 2
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [Pi.pow_apply]
    · ring
  have hu_deriv (t : Real) :
      HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (hu.differentiable_deriv_two t).hasDerivAt
  have hcoeff_int : IntervalIntegrable (fun t => 2 * w t * dw t)
      volume 0 L :=
    ((continuous_const.mul hw_cont).mul hdw_cont).intervalIntegrable 0 L
  have hsecond_int : IntervalIntegrable (fun t => deriv (deriv u) t)
      volume 0 L :=
    ((show ContDiff Real 1 (deriv u) from hu.deriv').continuous_deriv_one)
      |>.intervalIntegrable 0 L
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : Real)) (b := L)
    (u := fun t => w t ^ 2) (u' := fun t => 2 * w t * dw t)
    (v := deriv u) (v' := fun t => deriv (deriv u) t)
    (fun t _ => hw2_deriv t) (fun t _ => hu_deriv t)
    hcoeff_int hsecond_int
  have hweighted_eq :
      (∫ t in (0 : Real)..L, w t ^ 2 * deriv (deriv u) t) =
        ∫ t in (0 : Real)..L, q t := by
    rw [hibp]
    have hw0 : w 0 = 0 := by simp only [w, endpointExponentialWeight_zero]
    have hwL : w L = 0 := by simp only [w, endpointExponentialWeight_self]
    have hboundary : w L ^ 2 * deriv u L - w 0 ^ 2 * deriv u 0 = 0 := by
      rw [hw0, hwL]
      ring
    rw [hboundary, zero_sub]
    have hq_eq : q = fun t => -(2 * w t * dw t * deriv u t) := by
      funext t
      dsimp only [q]
      ring
    rw [hq_eq, intervalIntegral.integral_neg]
  have hq_cont : Continuous q := by
    dsimp only [q]
    exact (((continuous_const.mul hw_cont).mul hdw_cont).neg).mul hdu_cont
  have hm_nonneg : 0 ≤ L / 2 := by linarith
  have hm_le : L / 2 ≤ L := by linarith
  have hleft_point (t : Real) (ht : t ∈ Set.Icc (0 : Real) (L / 2)) :
      q t ≤ 2 * Real.sqrt (u 0) * w t * dw t +
        2 * t * Real.exp (-2 * t) := by
    have htL : t ∈ Set.Icc (0 : Real) L := ⟨ht.1, ht.2.trans hm_le⟩
    have hw := endpointExponentialWeight_mem_Icc htL
    have hdw : 0 ≤ dw t := endpointExponentialWeightDeriv_nonneg ht.2
    have hcoeff : 0 ≤ 2 * w t * dw t :=
      mul_nonneg (mul_nonneg (by norm_num) hw.1) hdw
    have hdu : -deriv u t ≤ Real.sqrt (u t) := by
      exact (neg_le_abs (deriv u t)).trans (hderiv_le t htL)
    have hfirst : q t ≤ (2 * w t * dw t) * Real.sqrt (u t) := by
      dsimp only [q]
      nlinarith [mul_le_mul_of_nonneg_left hdu hcoeff]
    have hsecond : (2 * w t * dw t) * Real.sqrt (u t) ≤
        (2 * w t * dw t) * (Real.sqrt (u 0) + t / 2) :=
      mul_le_mul_of_nonneg_left (hsqrt_left t ht) hcoeff
    have hdw_upper : dw t ≤ 2 * Real.exp (-2 * t) := by
      dsimp only [dw, endpointExponentialWeightDeriv]
      linarith [Real.exp_pos (-2 * (L - t))]
    have ht_nonneg : 0 ≤ t := ht.1
    have htail : t * w t * dw t ≤ 2 * t * Real.exp (-2 * t) := by
      have hmul := mul_le_mul hdw_upper hw.2 hw.1
        (by positivity : 0 ≤ 2 * Real.exp (-2 * t))
      nlinarith [mul_le_mul_of_nonneg_left hmul ht_nonneg]
    calc
      q t ≤ (2 * w t * dw t) * Real.sqrt (u t) := hfirst
      _ ≤ (2 * w t * dw t) * (Real.sqrt (u 0) + t / 2) := hsecond
      _ = 2 * Real.sqrt (u 0) * w t * dw t + t * w t * dw t := by ring
      _ ≤ 2 * Real.sqrt (u 0) * w t * dw t +
          2 * t * Real.exp (-2 * t) := add_le_add_right htail _
  have hright_point (t : Real) (ht : t ∈ Set.Icc (L / 2) L) :
      q t ≤ -2 * Real.sqrt (u L) * w t * dw t +
        2 * (L - t) * Real.exp (-2 * (L - t)) := by
    have htL : t ∈ Set.Icc (0 : Real) L := ⟨hm_nonneg.trans ht.1, ht.2⟩
    have hw := endpointExponentialWeight_mem_Icc htL
    have hdw : dw t ≤ 0 := endpointExponentialWeightDeriv_nonpos ht.1
    have hcoeff : 0 ≤ -(2 * w t * dw t) := by
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hw.1) hdw)
    have hdu : deriv u t ≤ Real.sqrt (u t) :=
      (le_abs_self (deriv u t)).trans (hderiv_le t htL)
    have hfirst : q t ≤ (-(2 * w t * dw t)) * Real.sqrt (u t) := by
      dsimp only [q]
      exact mul_le_mul_of_nonneg_left hdu hcoeff
    have hsecond : (-(2 * w t * dw t)) * Real.sqrt (u t) ≤
        (-(2 * w t * dw t)) * (Real.sqrt (u L) + (L - t) / 2) :=
      mul_le_mul_of_nonneg_left (hsqrt_right t ht) hcoeff
    have hdw_upper : -dw t ≤ 2 * Real.exp (-2 * (L - t)) := by
      dsimp only [dw, endpointExponentialWeightDeriv]
      linarith [Real.exp_pos (-2 * t)]
    have hLt_nonneg : 0 ≤ L - t := sub_nonneg.mpr ht.2
    have htail : -(L - t) * w t * dw t ≤
        2 * (L - t) * Real.exp (-2 * (L - t)) := by
      have hmul := mul_le_mul hdw_upper hw.2 hw.1
        (by positivity : 0 ≤ 2 * Real.exp (-2 * (L - t)))
      nlinarith [mul_le_mul_of_nonneg_left hmul hLt_nonneg]
    calc
      q t ≤ (-(2 * w t * dw t)) * Real.sqrt (u t) := hfirst
      _ ≤ (-(2 * w t * dw t)) *
          (Real.sqrt (u L) + (L - t) / 2) := hsecond
      _ = -2 * Real.sqrt (u L) * w t * dw t -
          (L - t) * w t * dw t := by ring
      _ ≤ -2 * Real.sqrt (u L) * w t * dw t +
          2 * (L - t) * Real.exp (-2 * (L - t)) := by linarith
  have hleft_bound_cont : Continuous (fun t : Real =>
      2 * Real.sqrt (u 0) * w t * dw t + 2 * t * Real.exp (-2 * t)) := by
    exact (((continuous_const.mul hw_cont).mul hdw_cont).add
      ((continuous_const.mul continuous_id').mul
        (continuous_const.mul continuous_id').rexp))
  have hright_bound_cont : Continuous (fun t : Real =>
      -2 * Real.sqrt (u L) * w t * dw t +
        2 * (L - t) * Real.exp (-2 * (L - t))) := by
    exact (((continuous_const.mul hw_cont).mul hdw_cont).add
      ((continuous_const.mul (continuous_const.sub continuous_id')).mul
        (continuous_const.mul (continuous_const.sub continuous_id')).rexp))
  have hleft_mono := intervalIntegral.integral_mono_on (μ := volume) hm_nonneg
    (hq_cont.intervalIntegrable 0 (L / 2))
    (hleft_bound_cont.intervalIntegrable 0 (L / 2)) hleft_point
  have hright_mono := intervalIntegral.integral_mono_on (μ := volume) hm_le
    (hq_cont.intervalIntegrable (L / 2) L)
    (hright_bound_cont.intervalIntegrable (L / 2) L) hright_point
  have hw_mid := endpointExponentialWeight_mem_Icc
    (show L / 2 ∈ Set.Icc (0 : Real) L from ⟨hm_nonneg, hm_le⟩)
  have hleft_bound :
      (∫ t in (0 : Real)..L / 2,
        2 * Real.sqrt (u 0) * w t * dw t +
          2 * t * Real.exp (-2 * t)) ≤ Real.sqrt (u 0) + 1 / 2 := by
    have hscale :
        (∫ t in (0 : Real)..L / 2,
          2 * Real.sqrt (u 0) * w t * dw t) =
          Real.sqrt (u 0) *
            ∫ t in (0 : Real)..L / 2, 2 * w t * dw t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [intervalIntegral.integral_add,
      hscale,
      integral_two_weight_mul_deriv,
      integral_two_mul_mul_exp_neg_two]
    · simp only [endpointExponentialWeight_zero]
      norm_num [Real.exp_zero]
      have hroot : 0 ≤ Real.sqrt (u 0) := Real.sqrt_nonneg _
      have hpotential : Real.sqrt (u 0) *
          endpointExponentialWeight L (L / 2) ^ 2 ≤ Real.sqrt (u 0) := by
        nlinarith [mul_le_mul_of_nonneg_left
          ((sq_le_one_iff₀ hw_mid.1).2 hw_mid.2) hroot]
      have htail : (-(1 / 2) + -(L / 2)) * Real.exp (-(2 * (L / 2))) +
          1 / 2 ≤ 1 / 2 := by
        have hnonpos : (-(1 / 2) + -(L / 2)) *
            Real.exp (-(2 * (L / 2))) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
            (Real.exp_pos _).le
        linarith
      linarith
    · exact (by fun_prop : Continuous
        (fun t : Real => 2 * Real.sqrt (u 0) * w t * dw t))
          |>.intervalIntegrable 0 (L / 2)
    · exact (by fun_prop : Continuous
        (fun t : Real => 2 * t * Real.exp (-2 * t)))
          |>.intervalIntegrable 0 (L / 2)
  have hright_bound :
      (∫ t in L / 2..L,
        -2 * Real.sqrt (u L) * w t * dw t +
          2 * (L - t) * Real.exp (-2 * (L - t))) ≤
        Real.sqrt (u L) + 1 / 2 := by
    have hscale :
        (∫ t in L / 2..L,
          -2 * Real.sqrt (u L) * w t * dw t) =
          -Real.sqrt (u L) *
            ∫ t in L / 2..L, 2 * w t * dw t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [intervalIntegral.integral_add,
      hscale,
      integral_two_weight_mul_deriv,
      integral_two_mul_reverse_mul_exp_neg_two]
    · simp only [endpointExponentialWeight_self]
      norm_num [Real.exp_zero]
      have hroot : 0 ≤ Real.sqrt (u L) := Real.sqrt_nonneg _
      have hpotential : Real.sqrt (u L) *
          endpointExponentialWeight L (L / 2) ^ 2 ≤ Real.sqrt (u L) := by
        nlinarith [mul_le_mul_of_nonneg_left
          ((sq_le_one_iff₀ hw_mid.1).2 hw_mid.2) hroot]
      have htail : 1 / 2 - (L - L / 2 + 1 / 2) *
          Real.exp (-(2 * (L - L / 2))) ≤ 1 / 2 := by
        have hexpterm' : 0 ≤ (L - L / 2 + 1 / 2) *
            Real.exp (-(2 * (L - L / 2))) := by
          positivity
        linarith
      linarith
    · exact (by fun_prop : Continuous
        (fun t : Real => -2 * Real.sqrt (u L) * w t * dw t))
          |>.intervalIntegrable (L / 2) L
    · exact (by fun_prop : Continuous
        (fun t : Real => 2 * (L - t) * Real.exp (-2 * (L - t))))
          |>.intervalIntegrable (L / 2) L
  have hq_split :
      (∫ t in (0 : Real)..L, q t) =
        (∫ t in (0 : Real)..L / 2, q t) +
          ∫ t in L / 2..L, q t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hq_cont.intervalIntegrable 0 (L / 2))
      (hq_cont.intervalIntegrable (L / 2) L)).symm
  calc
    (∫ t in (0 : Real)..L, endpointExponentialWeight L t ^ 2 *
        deriv (deriv u) t) = ∫ t in (0 : Real)..L, q t := hweighted_eq
    _ = (∫ t in (0 : Real)..L / 2, q t) +
        ∫ t in L / 2..L, q t := hq_split
    _ ≤ Real.sqrt (u 0) + Real.sqrt (u L) + 1 := by linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_potential_le_sq_distance
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) (p x : M) :
    f x ≤ 1 / 4 * ((riemannianEDistOf (I := I) g p x).toReal +
      2 * Real.sqrt (f p)) ^ 2 := by
  classical
  let : RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let d : Real := (riemannianEDistOf (I := I) g p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hf_nonneg (y : M) : 0 ≤ f y :=
    normalizedGradientRicciSoliton_potential_nonneg (I := I) h y
  have hε (ε : Real) (hεpos : 0 < ε) :
      f x ≤ 1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε := by
    let q : M → Real := fun y => f y + ε
    let u : M → Real := fun y => 2 * Real.sqrt (q y)
    have hq_pos (y : M) : 0 < q y := by
      dsimp only [q]
      linarith [hf_nonneg y]
    have hq_smooth : ContMDiff I (modelWithCornersSelf Real Real)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) q := by
      dsimp only [q]
      exact f.contMDiff.add contMDiff_const
    have hu_smooth : ContMDiff I (modelWithCornersSelf Real Real)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) u := by
      intro y
      exact contMDiffAt_const.mul
        ((Real.contDiffAt_sqrt (hq_pos y).ne').contMDiffAt.comp y
          (hq_smooth y))
    have hgrad_q (y : M) :
        gradFun (I := I) g q y = gradFun (I := I) g f y := by
      have hf_diff := (f.contMDiff y).mdifferentiableAt (by simp)
      change gradFun (I := I) g
        ((f : M → Real) + (fun _ : M => ε)) y = _
      rw [Operator.gradFun_add (I := I) g hf_diff mdifferentiableAt_const,
        Operator.gradFun_const]
      simp
    have hgrad_u (y : M) :
        gradFun (I := I) g u y =
          (Real.sqrt (q y))⁻¹ • gradFun (I := I) g f y := by
      have hq_diff := (hq_smooth y).mdifferentiableAt (by simp)
      have hsqrt_diff : DifferentiableAt Real Real.sqrt (q y) :=
        (Real.hasDerivAt_sqrt (hq_pos y).ne').differentiableAt
      have hcomp := Operator.gradFun_comp (I := I) g hsqrt_diff hq_diff
      have hsqrt_mdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
          (fun z : M => Real.sqrt (q z)) y :=
        ((Real.contDiffAt_sqrt (hq_pos y).ne').contMDiffAt.comp y
          (hq_smooth y)).mdifferentiableAt (by simp)
      have hscale := Operator.gradFun_const_smul (I := I) g 2
        hsqrt_mdiff
      have hu_eq : u = (2 : Real) • (fun z : M => Real.sqrt (q z)) := by
        funext z
        simp only [u, Pi.smul_apply, smul_eq_mul]
      calc
        gradFun (I := I) g u y =
            gradFun (I := I) g
              ((2 : Real) • (fun z : M => Real.sqrt (q z))) y :=
          congrArg (fun v : M → Real => gradFun (I := I) g v y) hu_eq
        _ = (2 : Real) • gradFun (I := I) g
            (fun z : M => Real.sqrt (q z)) y :=
          hscale
        _ = (Real.sqrt (q y))⁻¹ • gradFun (I := I) g f y := by
          rw [hcomp, hgrad_q,
            (Real.hasDerivAt_sqrt (hq_pos y).ne').deriv]
          rw [smul_smul]
          congr 1
          field_simp [(Real.sqrt_pos.2 (hq_pos y)).ne']
    have hgrad_u_bound (y : M) :
        Real.sqrt (g.inner y (gradFun (I := I) g u y)
          (gradFun (I := I) g u y)) ≤ 1 := by
      have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h y
      have hpot := normalizedGradientRicciSoliton_potential_equation
        (I := I) h y
      have hinner : g.inner y (gradFun (I := I) g f y)
          (gradFun (I := I) g f y) ≤ q y := by
        dsimp only [q]
        linarith
      have hsqrt := Real.sqrt_le_sqrt hinner
      rw [hgrad_u, sqrt_inner_smul, abs_inv,
        abs_of_pos (Real.sqrt_pos.2 (hq_pos y))]
      calc
        (Real.sqrt (q y))⁻¹ * Real.sqrt
            (g.inner y (gradFun (I := I) g f y)
              (gradFun (I := I) g f y)) ≤
            (Real.sqrt (q y))⁻¹ * Real.sqrt (q y) := by
          exact mul_le_mul_of_nonneg_left hsqrt
            (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 (hq_pos y)).ne'
    let K : NNReal := 1
    have hu_lip : ∀ y z : M, edist (u y) (u z) ≤
        (K : ENNReal) * riemannianEDistOf (I := I) g y z := by
      apply lip_of_grad_norm_le (I := I) g h.1 hu_smooth
      intro y
      simpa only [K, NNReal.coe_one] using hgrad_u_bound y
    have hfin : riemannianEDistOf (I := I) g p x ≠ (∞ : ENNReal) :=
      riemannianEDist_ne_top (I := I) p x
    have hu_real : |u p - u x| ≤ d := by
      have hrhs :
          (K : ENNReal) * riemannianEDistOf (I := I) g p x ≠
            (∞ : ENNReal) :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
      have hreal := ENNReal.toReal_mono hrhs (hu_lip p x)
      rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
        ENNReal.toReal_mul, ENNReal.coe_toReal, Real.dist_eq] at hreal
      simpa only [K, NNReal.coe_one, one_mul, d] using hreal
    have hu_nonneg (y : M) : 0 ≤ u y := by
      dsimp only [u]
      positivity
    have hu_growth : u x ≤ u p + d := by
      have habs : u x - u p ≤ |u p - u x| := by
        rw [abs_sub_comm]
        exact le_abs_self (u x - u p)
      linarith
    have hsq : u x ^ 2 ≤ (u p + d) ^ 2 := by
      exact (sq_le_sq₀ (hu_nonneg x)
        (add_nonneg (hu_nonneg p) hd)).2 hu_growth
    have hux_sq : u x ^ 2 = 4 * (f x + ε) := by
      dsimp only [u, q]
      rw [mul_pow, Real.sq_sqrt]
      · ring
      · linarith [hf_nonneg x]
    dsimp only [u, q] at hsq
    rw [hux_sq] at hsq
    nlinarith
  have hseq : Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htend : Tendsto
      (fun n : Nat =>
        1 / 4 * (d + 2 * Real.sqrt
          (f p + (1 : Real) / ((n : Real) + 1))) ^ 2 -
            (1 : Real) / ((n : Real) + 1))
      atTop (𝓝 (1 / 4 * (d + 2 * Real.sqrt (f p)) ^ 2)) := by
    have hcont : ContinuousAt
      (fun ε : Real => 1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε)
        0 := by
      fun_prop
    have htend' : Tendsto
        (fun n : Nat =>
          1 / 4 * (d + 2 * Real.sqrt
            (f p + (1 : Real) / ((n : Real) + 1))) ^ 2 -
              (1 : Real) / ((n : Real) + 1))
        atTop
        (𝓝 ((fun ε : Real =>
          1 / 4 * (d + 2 * Real.sqrt (f p + ε)) ^ 2 - ε) 0)) := by
      apply Filter.Tendsto.congr'
        (Filter.Eventually.of_forall fun n => rfl)
      exact hcont.tendsto.comp hseq
    simpa only [add_zero, sub_zero] using htend'
  have hlim : f x ≤ 1 / 4 * (d + 2 * Real.sqrt (f p)) ^ 2 := by
    apply ge_of_tendsto htend
    exact Filter.Eventually.of_forall fun n => hε _ (by positivity)
  simpa only [d] using hlim

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem sqrt_potential_two_point
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {p q : M} (hpq : p ≠ q) :
    1 / 2 * (riemannianEDistOf (I := I) g p q).toReal + 1 / 4 -
        2 * (Module.finrank Real E : Real) ≤
      Real.sqrt (f p) + Real.sqrt (f q) := by
  classical
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := h.1.complete
  let hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨gamma, L, hL, hgamma_zero, hgamma_end, hgamma_smooth,
      hgamma_geo, hgamma_unit, hgamma_min, hdist⟩ :=
    exists_smooth_unit_speed_minimizing_geodesic_between_points_of_ne
      (I := I) g hEnorm p q hpq
  have hL_dist : L = (riemannianEDistOf (I := I) g p q).toReal := by
    change L = (riemannianEDist I p q).toReal
    rw [hdist, ENNReal.toReal_ofReal hL.le]
  have hgamma_C1 (a b : Real) :
      ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc a b) :=
    hgamma_smooth.contMDiffOn.of_le (by simp)
  have hgamma_length (a b : Real) :
      Riemannian.Variation.arcLength (I := I) g gamma a b = b - a := by
    unfold Riemannian.Variation.arcLength
    calc
      (∫ t in a..b,
          Real.sqrt (g.inner (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))) =
          ∫ _t in a..b, (1 : Real) := by
        apply intervalIntegral.integral_congr
        intro t _
        change Real.sqrt (g.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) = 1
        rw [hgamma_unit t, Real.sqrt_one]
      _ = b - a := by simp
  have hdist_left {t : Real} (ht : t ∈ Set.Icc (0 : Real) L) :
      (riemannianEDistOf (I := I) g p (gamma t)).toReal ≤ t := by
    have hed := Riemannian.Geodesic.riemannianEDist_le_arcLength
      (I := I) g ht.1 (hgamma_C1 0 t)
        (fun s _ => hEnorm (gamma s) _)
    rw [hgamma_zero, hgamma_length] at hed
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    simpa only [sub_zero, ENNReal.toReal_ofReal ht.1, riemannianEDistOf]
      using hreal
  have hdist_right {t : Real} (ht : t ∈ Set.Icc (0 : Real) L) :
      (riemannianEDistOf (I := I) g q (gamma t)).toReal ≤ L - t := by
    have hed := Riemannian.Geodesic.riemannianEDist_le_arcLength
      (I := I) g ht.2 (hgamma_C1 t L)
        (fun s _ => hEnorm (gamma s) _)
    rw [hgamma_end, hgamma_length, riemannianEDist_comm] at hed
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2),
      riemannianEDistOf] using hreal
  let u : Real → Real := fun t => f (gamma t)
  have huM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ u := by
    dsimp only [u]
    exact f.contMDiff.comp hgamma_smooth
  have hu : ContDiff Real 2 u :=
    (contMDiff_iff_contDiff.mp huM).of_le
      (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hu_nonneg (t : Real) : 0 ≤ u t :=
    normalizedGradientRicciSoliton_potential_nonneg (I := I) h (gamma t)
  have hderiv_le (t : Real) : |deriv u t| ≤ Real.sqrt (u t) := by
    have hderiv := deriv_comp_eq_inner_grad_velocity
      (I := I) g f.contMDiff hgamma_smooth t
    have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g (gamma t)
      (gradFun (I := I) g f (gamma t))
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
    rw [hgamma_unit t, Real.sqrt_one, mul_one] at hcs
    have hR := normalizedGradientRicciSoliton_scalar_nonneg (I := I) h (gamma t)
    have hpot := normalizedGradientRicciSoliton_potential_equation
      (I := I) h (gamma t)
    have hgrad : g.inner (gamma t)
        (gradFun (I := I) g f (gamma t))
        (gradFun (I := I) g f (gamma t)) ≤ f (gamma t) := by
      linarith
    change |deriv ((f : M → Real) ∘ gamma) t| ≤ Real.sqrt (f (gamma t))
    rw [hderiv]
    exact hcs.trans (Real.sqrt_le_sqrt hgrad)
  have hsqrt_left (t : Real) (ht : t ∈ Set.Icc (0 : Real) (L / 2)) :
      Real.sqrt (u t) ≤ Real.sqrt (u 0) + t / 2 := by
    have htL : t ∈ Set.Icc (0 : Real) L := ⟨ht.1, ht.2.trans (by linarith)⟩
    have hupper := normalizedGradientRicciSoliton_potential_le_sq_distance
      (I := I) h p (gamma t)
    have hd_nonneg : 0 ≤
        (riemannianEDistOf (I := I) g p (gamma t)).toReal :=
      ENNReal.toReal_nonneg
    have hsum_nonneg : 0 ≤ t + 2 * Real.sqrt (f p) := by
      nlinarith [ht.1, Real.sqrt_nonneg (f p)]
    have hsum_le :
        (riemannianEDistOf (I := I) g p (gamma t)).toReal +
            2 * Real.sqrt (f p) ≤ t + 2 * Real.sqrt (f p) := by
      linarith [hdist_left htL]
    have hsq := (sq_le_sq₀
      (add_nonneg hd_nonneg (by positivity)) hsum_nonneg).2 hsum_le
    have hf_le : f (gamma t) ≤ 1 / 4 *
        (t + 2 * Real.sqrt (f p)) ^ 2 :=
      hupper.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
    have htarget_nonneg : 0 ≤ Real.sqrt (f p) + t / 2 := by
      nlinarith [ht.1, Real.sqrt_nonneg (f p)]
    have hu_zero : u 0 = f p := by simp only [u, hgamma_zero]
    rw [hu_zero]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) htarget_nonneg).mp
    rw [Real.sq_sqrt (hu_nonneg t)]
    change f (gamma t) ≤ _
    nlinarith
  have hsqrt_right (t : Real) (ht : t ∈ Set.Icc (L / 2) L) :
      Real.sqrt (u t) ≤ Real.sqrt (u L) + (L - t) / 2 := by
    have hm_nonneg : 0 ≤ L / 2 := by linarith [hL]
    have htL : t ∈ Set.Icc (0 : Real) L := ⟨hm_nonneg.trans ht.1, ht.2⟩
    have hupper := normalizedGradientRicciSoliton_potential_le_sq_distance
      (I := I) h q (gamma t)
    have hd_nonneg : 0 ≤
        (riemannianEDistOf (I := I) g q (gamma t)).toReal :=
      ENNReal.toReal_nonneg
    have hLt : 0 ≤ L - t := sub_nonneg.mpr ht.2
    have hsum_nonneg : 0 ≤ L - t + 2 * Real.sqrt (f q) := by positivity
    have hsum_le :
        (riemannianEDistOf (I := I) g q (gamma t)).toReal +
            2 * Real.sqrt (f q) ≤ L - t + 2 * Real.sqrt (f q) := by
      linarith [hdist_right htL]
    have hsq := (sq_le_sq₀
      (add_nonneg hd_nonneg (by positivity)) hsum_nonneg).2 hsum_le
    have hf_le : f (gamma t) ≤ 1 / 4 *
        (L - t + 2 * Real.sqrt (f q)) ^ 2 :=
      hupper.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))
    have htarget_nonneg : 0 ≤ Real.sqrt (f q) + (L - t) / 2 := by positivity
    have hu_end : u L = f q := by simp only [u, hgamma_end]
    rw [hu_end]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) htarget_nonneg).mp
    rw [Real.sq_sqrt (hu_nonneg t)]
    change f (gamma t) ≤ _
    nlinarith
  let phi : Real → Real := endpointExponentialWeight L
  have hphi : ContDiff Real ∞ phi := by
    dsimp only [phi]
    unfold endpointExponentialWeight
    fun_prop
  have hphi_zero : phi 0 = 0 := endpointExponentialWeight_zero L
  have hphi_end : phi L = 0 := endpointExponentialWeight_self L
  have hRic := Riemannian.Variation.weighted_ricci_integral_le_of_minimising_geodesic
    (I := I) g h.1 gamma hL hgamma_smooth
      (hgamma_geo.isGeodesicOn (Set.Icc 0 L)) hgamma_min
      (fun t _ => hgamma_unit t) phi hphi hphi_zero hphi_end
  have hn_one : 0 ≤ (Module.finrank Real E : Real) - 1 := by
    have hn : (1 : Real) ≤ Module.finrank Real E := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank Real E))
    linarith
  have hphi_deriv_integral :
      (∫ t in (0 : Real)..L, deriv phi t ^ 2) =
        ∫ t in (0 : Real)..L, endpointExponentialWeightDeriv L t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    change deriv phi t ^ 2 = endpointExponentialWeightDeriv L t ^ 2
    rw [show deriv phi t = endpointExponentialWeightDeriv L t by
      simpa only [phi] using endpointExponentialWeight_deriv L t]
  have hRic_upper :
      (∫ t in (0 : Real)..L, phi t ^ 2 *
        ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) ≤
        2 * ((Module.finrank Real E : Real) - 1) := by
    rw [hphi_deriv_integral] at hRic
    calc
      _ ≤ ((Module.finrank Real E : Real) - 1) *
          ∫ t in (0 : Real)..L, endpointExponentialWeightDeriv L t ^ 2 := hRic
      _ ≤ ((Module.finrank Real E : Real) - 1) * 2 :=
        mul_le_mul_of_nonneg_left
          (endpointExponentialWeightDeriv_sq_integral_le hL.le) hn_one
      _ = 2 * ((Module.finrank Real E : Real) - 1) := by ring
  have hsecond (t : Real) : deriv (deriv u) t =
      hessFun (I := I) g f (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) := by
    change (deriv^[2] ((f : M → Real) ∘ gamma)) t = _
    exact deriv2_comp_geo_at (I := I) g f.contMDiff hgamma_smooth
      (hgamma_geo t)
  have hRic_point (t : Real) :
      ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) =
        1 / 2 - deriv (deriv u) t := by
    have hsol := h.2.1 (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
    rw [hgamma_unit t, ← hsecond t] at hsol
    norm_num at hsol ⊢
    linarith
  have hphi_cont : Continuous phi := hphi.continuous
  have hsecond_cont : Continuous (fun t => deriv (deriv u) t) :=
    ((show ContDiff Real 1 (deriv u) from hu.deriv').continuous_deriv_one)
  have hRic_integral :
      (∫ t in (0 : Real)..L, phi t ^ 2 *
        ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) =
        1 / 2 * (∫ t in (0 : Real)..L, phi t ^ 2) -
          ∫ t in (0 : Real)..L, phi t ^ 2 * deriv (deriv u) t := by
    calc
      _ = ∫ t in (0 : Real)..L,
          1 / 2 * phi t ^ 2 - phi t ^ 2 * deriv (deriv u) t := by
        apply intervalIntegral.integral_congr
        intro t _
        change phi t ^ 2 *
          ricciTensor (I := I) g (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) =
          1 / 2 * phi t ^ 2 - phi t ^ 2 * deriv (deriv u) t
        rw [hRic_point t]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub,
          intervalIntegral.integral_const_mul]
        · exact ((hphi_cont.pow 2).const_mul _).intervalIntegrable 0 L
        · exact ((hphi_cont.pow 2).mul hsecond_cont).intervalIntegrable 0 L
  have hsecond_upper :
      (∫ t in (0 : Real)..L, phi t ^ 2 * deriv (deriv u) t) ≤
        Real.sqrt (f p) + Real.sqrt (f q) + 1 := by
    have hbound := endpointExponentialWeight_second_deriv_integral_le
      hL.le u hu (fun t _ => hderiv_le t) hsqrt_left hsqrt_right
    simpa only [phi, u, hgamma_zero, hgamma_end] using hbound
  have hphi_lower : L - 3 / 2 ≤ ∫ t in (0 : Real)..L, phi t ^ 2 := by
    have hdef := endpointExponentialWeight_sq_deficit_integral_le hL.le
    have hcont : Continuous (fun t : Real => endpointExponentialWeight L t ^ 2) := by
      unfold endpointExponentialWeight
      fun_prop
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_const, smul_eq_mul] at hdef
    · norm_num at hdef
      change L - 3 / 2 ≤
        ∫ t in (0 : Real)..L, endpointExponentialWeight L t ^ 2
      linarith
    · exact continuous_const.intervalIntegrable 0 L
    · exact hcont.intervalIntegrable 0 L
  rw [hRic_integral] at hRic_upper
  rw [← hL_dist]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_potential_tendsto_cocompact_atTop
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    Tendsto (f : M → Real) (cocompact M) atTop := by
  classical
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := h.1.complete
  let _ : MetricSpace M :=
    Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M :=
    Riemannian.HopfRinow.properSpace_riemMetric_of_complete_metric
      (I := I) (M := M) g h.1
  let p : M := Classical.choice (inferInstance : Nonempty M)
  let d : M → Real := fun x =>
    (riemannianEDistOf (I := I) g p x).toReal
  have hdist : Tendsto d (cocompact M) atTop := by
    have heq : d = dist p := by
      funext x
      change (riemannianEDist I p x).toReal = dist p x
      exact (Riemannian.HopfRinow.riemMetric_dist_eq
        (I := I) (M := M) p x).symm
    rw [heq]
    exact tendsto_dist_left_cocompact_atTop p
  have hlinear : Tendsto
      (fun x : M => 1 / 2 * d x + 1 / 4 -
        2 * (Module.finrank Real E : Real) - Real.sqrt (f p))
      (cocompact M) atTop := by
    rw [tendsto_atTop] at hdist ⊢
    intro b
    filter_upwards [hdist
      (2 * (b - 1 / 4 + 2 * (Module.finrank Real E : Real) +
        Real.sqrt (f p)))] with x hx
    nlinarith
  have hlinear_le (x : M) :
      1 / 2 * d x + 1 / 4 - 2 * (Module.finrank Real E : Real) -
          Real.sqrt (f p) ≤ Real.sqrt (f x) := by
    by_cases hpx : p = x
    · subst x
      have hn : (1 : Real) ≤ Module.finrank Real E := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (NeZero.ne (Module.finrank Real E))
      change 1 / 2 * (riemannianEDistOf (I := I) g p p).toReal +
          1 / 4 - 2 * (Module.finrank Real E : Real) - Real.sqrt (f p) ≤
        Real.sqrt (f p)
      rw [riemannianEDistOf_self, ENNReal.toReal_zero]
      nlinarith [Real.sqrt_nonneg (f p)]
    · have htwo := sqrt_potential_two_point (I := I) h hpx
      dsimp only [d]
      linarith
  have hsqrt : Tendsto (fun x : M => Real.sqrt (f x))
      (cocompact M) atTop :=
    tendsto_atTop_mono hlinear_le hlinear
  apply tendsto_atTop_mono' (cocompact M) ?_ hsqrt
  filter_upwards [hsqrt.eventually_ge_atTop 1] with x hx
  have hfx := normalizedGradientRicciSoliton_potential_nonneg (I := I) h x
  calc
    Real.sqrt (f x) ≤ Real.sqrt (f x) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (f x)]
    _ = f x := Real.sq_sqrt hfx

theorem normalizedGradientRicciSoliton_potential_isProperMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    IsProperMap (f : M → Real) := by
  rw [isProperMap_iff_tendsto_cocompact]
  exact ⟨f.contMDiff.continuous,
    (normalizedGradientRicciSoliton_potential_tendsto_cocompact_atTop
      (I := I) h).trans atTop_le_cocompact⟩

theorem normalizedGradientRicciSoliton_exists_potential_minimizer
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    ∃ o : M, IsMinOn (f : M → Real) Set.univ o := by
  obtain ⟨o, ho⟩ := f.contMDiff.continuous.exists_forall_le
    (normalizedGradientRicciSoliton_potential_tendsto_cocompact_atTop
      (I := I) h)
  exact ⟨o, fun _ _ => ho _⟩

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_potential_eq_scalar_of_isLocalMin
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsLocalMin (f : M → Real) o) :
    f o = metricScalarAt (I := I) g o := by
  have hgrad : gradFun (I := I) g f o = 0 :=
    gradientFun_eq_zero_at_spatial_min (I := I) g ho
      ((f.contMDiff o).mdifferentiableAt (by simp))
  have hpot := normalizedGradientRicciSoliton_potential_equation (I := I) h o
  rw [hgrad] at hpot
  simpa only [map_zero, add_zero] using hpot.symm

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsLocalMin (f : M → Real) o) :
    f o ≤ (Module.finrank Real E : Real) / 2 := by
  have hf_mdiff : MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) o :=
    (f.contMDiff o).mdifferentiableAt (by simp)
  have hf_eventually : ∀ᶠ y in 𝓝 o,
      MDifferentiableAt I 𝓘(Real, Real) (f : M → Real) y :=
    Filter.Eventually.of_forall fun y =>
      (f.contMDiff y).mdifferentiableAt (by simp)
  have hgrad : MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g f y) o :=
    (gradientFun_contMDiffAt (I := I) g (f.contMDiff o)).mdifferentiableAt
      (by simp)
  have hmetric : IsMetricCompatible (I := I)
      (LeviCivita (I := I) g) g := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hlap : 0 ≤ ΔG (I := I) g f o := by
    have hlap' : 0 ≤ laplacian (I := I) (LeviCivita (I := I) g) g f o :=
      laplacian_nonneg_at_spatial_min_of_metricCompatible
        (I := I) (LeviCivita (I := I) g) g hmetric
          ho hf_mdiff hf_eventually hgrad
    rw [laplacian_levi_eq (I := I) g f.contMDiff o] at hlap'
    exact hlap'
  have htrace := gradientRicciSoliton_trace (I := I) h.2.1 o
  have hfo :=
    normalizedGradientRicciSoliton_potential_eq_scalar_of_isLocalMin
      (I := I) h ho
  rw [hfo]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
theorem normalizedGradientRicciSoliton_potential_le_sq_distance_of_isMinOn
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsMinOn (f : M → Real) Set.univ o) (x : M) :
    f x ≤ 1 / 4 * ((riemannianEDistOf (I := I) g o x).toReal +
      Real.sqrt (2 * (Module.finrank Real E : Real))) ^ 2 := by
  have hlocal : IsLocalMin (f : M → Real) o := ho.isLocalMin univ_mem
  have hfo :=
    normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
      (I := I) h hlocal
  have hfo_nonneg := normalizedGradientRicciSoliton_potential_nonneg
    (I := I) h o
  have hn : 0 ≤ (Module.finrank Real E : Real) := by positivity
  have hsqrt : 2 * Real.sqrt (f o) ≤
      Real.sqrt (2 * (Module.finrank Real E : Real)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hfo_nonneg, Real.sq_sqrt (by positivity)]
    nlinarith
  have hbase := normalizedGradientRicciSoliton_potential_le_sq_distance
    (I := I) h o x
  have hd : 0 ≤ (riemannianEDistOf (I := I) g o x).toReal :=
    ENNReal.toReal_nonneg
  have hsq :
      ((riemannianEDistOf (I := I) g o x).toReal +
          2 * Real.sqrt (f o)) ^ 2 ≤
        ((riemannianEDistOf (I := I) g o x).toReal +
          Real.sqrt (2 * (Module.finrank Real E : Real))) ^ 2 := by
    apply (sq_le_sq₀ (add_nonneg hd (by positivity))
      (add_nonneg hd (Real.sqrt_nonneg _))).2
    linarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hsq (by norm_num))

theorem normalizedGradientRicciSoliton_sq_distance_le_potential_of_isMinOn
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) {o : M}
    (ho : IsMinOn (f : M → Real) Set.univ o) (x : M) :
    1 / 4 * (max
      ((riemannianEDistOf (I := I) g o x).toReal -
        5 * (Module.finrank Real E : Real)) 0) ^ 2 ≤ f x := by
  let n : Real := Module.finrank Real E
  let d : Real := (riemannianEDistOf (I := I) g o x).toReal
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (NeZero.ne (Module.finrank Real E))
  have hfo_nonneg := normalizedGradientRicciSoliton_potential_nonneg
    (I := I) h o
  have hfx_nonneg := normalizedGradientRicciSoliton_potential_nonneg
    (I := I) h x
  have hlocal : IsLocalMin (f : M → Real) o := ho.isLocalMin univ_mem
  have hfo_le :=
    normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
      (I := I) h hlocal
  change f o ≤ n / 2 at hfo_le
  have hsqrt_fo : Real.sqrt (f o) ≤ n / 2 + 1 / 4 := by
    have hsqrt_sq : Real.sqrt (f o) ^ 2 = f o := Real.sq_sqrt hfo_nonneg
    nlinarith [sq_nonneg (Real.sqrt (f o) - 1 / 2)]
  by_cases hd : d ≤ 5 * n
  · have harg : d - 5 * n ≤ 0 := by linarith
    change 1 / 4 * (max (d - 5 * n) 0) ^ 2 ≤ f x
    rw [max_eq_right harg]
    norm_num
    exact hfx_nonneg
  · have hdpos : 5 * n < d := lt_of_not_ge hd
    have hdist_pos : 0 < d := by nlinarith
    have hox : o ≠ x := by
      intro hox
      subst x
      dsimp only [d] at hdist_pos
      rw [riemannianEDistOf_self, ENNReal.toReal_zero] at hdist_pos
      exact (lt_irrefl 0 hdist_pos)
    have htwo := sqrt_potential_two_point (I := I) h hox
    change 1 / 2 * d + 1 / 4 - 2 * n ≤
      Real.sqrt (f o) + Real.sqrt (f x) at htwo
    have hroot : 1 / 2 * (d - 5 * n) ≤ Real.sqrt (f x) := by
      nlinarith
    have harg_nonneg : 0 ≤ d - 5 * n := by linarith
    have hleft_nonneg : 0 ≤ 1 / 2 * (d - 5 * n) := by positivity
    have hsquare := (sq_le_sq₀ hleft_nonneg (Real.sqrt_nonneg _)).2 hroot
    rw [Real.sq_sqrt hfx_nonneg] at hsquare
    change 1 / 4 * (max (d - 5 * n) 0) ^ 2 ≤ f x
    rw [max_eq_left harg_nonneg]
    nlinarith

theorem normalizedGradientRicciSoliton_exists_potential_minimizer_with_growth
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    ∃ o : M,
      IsMinOn (f : M → Real) Set.univ o ∧
        (∀ x : M,
          1 / 4 * (max
            ((riemannianEDistOf (I := I) g o x).toReal -
              5 * (Module.finrank Real E : Real)) 0) ^ 2 ≤ f x ∧
          f x ≤ 1 / 4 *
            ((riemannianEDistOf (I := I) g o x).toReal +
              Real.sqrt (2 * (Module.finrank Real E : Real))) ^ 2) ∧
        0 ≤ f o ∧
        f o = metricScalarAt (I := I) g o ∧
        f o ≤ (Module.finrank Real E : Real) / 2 := by
  obtain ⟨o, ho⟩ :=
    normalizedGradientRicciSoliton_exists_potential_minimizer (I := I) h
  have hlocal : IsLocalMin (f : M → Real) o := ho.isLocalMin univ_mem
  refine ⟨o, ho, ?_,
    normalizedGradientRicciSoliton_potential_nonneg (I := I) h o,
    normalizedGradientRicciSoliton_potential_eq_scalar_of_isLocalMin
      (I := I) h hlocal,
    normalizedGradientRicciSoliton_potential_le_finrank_div_two_of_isLocalMin
      (I := I) h hlocal⟩
  intro x
  exact ⟨
    normalizedGradientRicciSoliton_sq_distance_le_potential_of_isMinOn
      (I := I) h ho x,
    normalizedGradientRicciSoliton_potential_le_sq_distance_of_isMinOn
      (I := I) h ho x⟩

end DifferentialGeometry.Geometry
