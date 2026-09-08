import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lLength_ge_of_scalar_lower_bound
    (S : SolutionOn (I := I) (M := M) D)
    (T a b K : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (gamma : ℝ → M)
    (hR : ∀ s ∈ Icc a b, -K ≤ S.scalar (T - s) (gamma s))
    (hInt : IntervalIntegrable (lDensity S T gamma) volume a b) :
    -(2 * K / 3) *
        (b * Real.sqrt b - a * Real.sqrt a) ≤
      lLength S T gamma a b := by
  have hb : 0 ≤ b := ha.trans hab
  have hsqrtInt :
      (∫ s in a..b, Real.sqrt s) =
        (2 / 3 : ℝ) *
          (b * Real.sqrt b - a * Real.sqrt a) := by
    have hbpow : b ^ ((1 / 2 : ℝ) + 1) = b * Real.sqrt b := by
      rw [Real.rpow_add' hb (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      ring
    have hapow : a ^ ((1 / 2 : ℝ) + 1) = a * Real.sqrt a := by
      rw [Real.rpow_add' ha (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      ring
    calc
      (∫ s in a..b, Real.sqrt s) =
          ∫ s in a..b, s ^ (1 / 2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact Real.sqrt_eq_rpow s
      _ = (b ^ ((1 / 2 : ℝ) + 1) -
            a ^ ((1 / 2 : ℝ) + 1)) / ((1 / 2 : ℝ) + 1) :=
        integral_rpow (Or.inl (by norm_num))
      _ = (2 / 3 : ℝ) *
          (b * Real.sqrt b - a * Real.sqrt a) := by
        rw [hbpow, hapow]
        ring
  have hleftInt : IntervalIntegrable
      (fun s : ℝ ↦ -K * Real.sqrt s) volume a b :=
    (show Continuous (fun s : ℝ ↦ -K * Real.sqrt s) from
      continuous_const.mul Real.continuous_sqrt).intervalIntegrable
        (μ := volume) a b
  have hpoint : ∀ s ∈ Icc a b,
      -K * Real.sqrt s ≤ lDensity S T gamma s := by
    intro s hs
    have hspeed : 0 ≤ lSpeedSq S T gamma s :=
      lSpeedSq_nonneg S T gamma s
    calc
      -K * Real.sqrt s = Real.sqrt s * (-K) := by ring
      _ ≤ Real.sqrt s *
          (S.scalar (T - s) (gamma s) + lSpeedSq S T gamma s) :=
        mul_le_mul_of_nonneg_left
          ((hR s hs).trans (le_add_of_nonneg_right hspeed))
          (Real.sqrt_nonneg s)
      _ = lDensity S T gamma s := rfl
  have hmono := intervalIntegral.integral_mono_on hab hleftInt hInt hpoint
  calc
    -(2 * K / 3) * (b * Real.sqrt b - a * Real.sqrt a) =
        -K * ((2 / 3 : ℝ) *
          (b * Real.sqrt b - a * Real.sqrt a)) := by ring
    _ = -K * (∫ s in a..b, Real.sqrt s) := by rw [hsqrtInt]
    _ = ∫ s in a..b, -K * Real.sqrt s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in a..b, lDensity S T gamma s := hmono
    _ = lLength S T gamma a b := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
