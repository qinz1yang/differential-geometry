import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.TimeWeighted
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open MeasureTheory Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem exists_integrable_nablaRic_bound_on_initial_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C : ℝ}
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) :
    ∃ F : ℝ → ℝ, IntervalIntegrable F volume a b ∧
      ∀ t ∈ Ioc a b, ∀ x : M,
        Real.sqrt (Tensor0SBundle.normSq0S (S.family.metric t) x 3
          (ricCovTower (S.family.metric t) (S.family.metric t) 1 x)) ≤ F t := by
  obtain ⟨A, hA, hbound⟩ := exists_time_weighted_curvature_derivative_bound
    S hS hcarrier hregular hcomplete hC hcurv 1
  let B := (Module.finrank ℝ E : ℝ) ^ 5 * A
  refine ⟨fun t => Real.sqrt B * (t - a) ^ (-(1 / 2 : ℝ)), ?_, ?_⟩
  · have hpow : IntervalIntegrable (fun t : ℝ => (t - a) ^ (-(1 / 2 : ℝ)))
        volume a b := by
      simpa only [zero_add, sub_add_cancel] using
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b - a)
          (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_right a
    exact hpow.const_mul (Real.sqrt B)
  · intro t ht x
    have hpos : 0 < t - a := sub_pos.mpr ht.1
    have htower := ricTower_normSq_le S t 1 x
    have hw := hbound t ht x
    simp only [pow_one] at hw
    have hnonneg : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 5 := by positivity
    have hm := mul_le_mul_of_nonneg_left hw hnonneg
    have hraw : Tensor0SBundle.normSq0S (S.family.metric t) x 3
        (ricCovTower (S.family.metric t) (S.family.metric t) 1 x) ≤ B / (t - a) := by
      apply (le_div_iff₀ hpos).mpr
      calc
        _ ≤ ((Module.finrank ℝ E : ℝ) ^ 5 * nablaKRm04NormSqIntrinsic S 1 t x) *
            (t - a) := mul_le_mul_of_nonneg_right htower hpos.le
        _ ≤ B := by simpa only [B, mul_assoc, mul_left_comm, mul_comm] using hm
    calc
      _ ≤ Real.sqrt (B / (t - a)) := Real.sqrt_le_sqrt hraw
      _ = Real.sqrt B * (t - a) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_div' B hpos.le, Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow,
          div_eq_mul_inv]

end DifferentialGeometry.PDE.RicciFlow
