import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedEarlyScalarCXSP
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# CX-SPINE: a seed scalar counterexample sequence has unbounded query times

The bounded-time estimate is produced from the actual prepared chain inside
the proof. The sequence carries its own small seeds and normalized scalar
escape; no non-Good sequence from P6(b) is used.
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- The scalar counterexample sequence for P6(c) must escape every bounded time
interval. Its scale and scalar escape hypotheses are those of that sequence. -/
theorem seed_bad_times_tendsto_atTop_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (A : ℝ) (hA : 0 < A)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
    (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ)
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
      (t i) (p i) (r i))
    (hx : ∀ i, x i ∈ riemannianBallOf
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i))
    (hscale : ∀ i, r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1))
    (hbad : Tendsto (fun i =>
      let H := (F.tower.history (idx i)).toHistory
      metricScalarAt (H.stageMetric (H.activeStage (t i)) (t i)) (x i) * (r i) ^ 2)
      atTop atTop) :
    Tendsto (fun i => (t i : ℝ)) atTop atTop := by
  have hinv : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_atTop.mpr
  intro B
  let N : ℕ := max 1 ⌈B⌉₊
  have hN : 1 ≤ N := le_max_left _ _
  have hBN : B ≤ (N : ℝ) := (Nat.le_ceil B).trans (by
    exact_mod_cast (le_max_right (1 : ℕ) ⌈B⌉₊))
  obtain ⟨rbar, K, hrbar, _hK, hearly⟩ := exists_prepared_early_scalar_bound_CXSP
    S F hTower N hN A hA
  have hfrac : ∀ᶠ i : ℕ in atTop, 1 / ((i : ℝ) + 1) < rbar :=
    hinv.eventually (Iio_mem_nhds hrbar)
  filter_upwards [hfrac, hbad.eventually_gt_atTop K] with i hi hRi
  by_contra hnot
  have htiB : (t i : ℝ) ≤ B := (lt_of_not_ge hnot).le
  have hri : r i ≤ rbar * Real.sqrt (t i : ℝ) := calc
    r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1) := hscale i
    _ = (1 / ((i : ℝ) + 1)) * Real.sqrt (t i : ℝ) := by ring
    _ ≤ rbar * Real.sqrt (t i : ℝ) :=
      mul_le_mul_of_nonneg_right hi.le (Real.sqrt_nonneg _)
  have hbound := hearly (idx i) (t i) (p i) (r i) (htiB.trans hBN) hri
    (hsmall i) (x i) (hx i)
  have hr : 0 < r i := (hsmall i).1
  have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg (r i))
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), mul_one] at hmul
  exact (not_lt_of_ge hmul) hRi

end GC.LongTime.Ch11
