import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- The original globally lower-bounded action has the sharper recent-time
lower bound. The change of scalar floor preserves its entire action-value set,
including infinite actions and the case of no admissible competitor. -/
theorem regularizedCost_ge_recent_half_time_of_cutoff_records
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v)
    (hvr : v ^ 2 ≤ r ^ 2 / 2) (hT : 2 * r ^ 2 < T)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    ((-2 * v ^ 3 / r ^ 2 : ℝ) : WithTop ℝ) ≤
      H.regularizedCost first last hle T (3 / a₀) 0 v p q := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hT0 : 0 < T := by nlinarith
  let B : ℝ := 3 / (a₀ + T / 2)
  have hden : 0 < a₀ + T / 2 := by positivity
  have hclock (j : H.StageInterval first last) (t : ℝ)
      (ht : t ∈ Ioo (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T v j.val)) :
      T / 2 ≤ T - t ^ 2 := by
    have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht.1.le
    have hend : H.regularizedStageEnd T v j.val ≤ v := by
      have hh : T - max (T - v ^ 2) (H.time j.val) ≤ v ^ 2 := by
        have hm := le_max_left (T - v ^ 2) (H.time j.val)
        linarith
      exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_sq hv)
    have htv : t ≤ v := ht.2.le.trans hend
    have ht2 : t ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ ht0 htv 2
    nlinarith
  have hHI := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  have hfloors (j : H.StageInterval first last) (t : ℝ)
      (ht : t ∈ Ioo (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T v j.val)) (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x ∧
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x := by
    have hrecent := hclock j t ht
    have htime0 : 0 ≤ T - t ^ 2 := by linarith
    have htimeDen : 0 < a₀ + (T - t ^ 2) := by linarith
    have hs := H.mapsTo_regularizedStage_Ioo T 0 v j.val ht
    have hR := (hHI.1 j.val (T - t ^ 2) hs x).2
    have hglobal : 3 / (a₀ + (T - t ^ 2)) ≤ 3 / a₀ := by
      apply (div_le_div_iff₀ htimeDen ha₀).mpr
      linarith
    have hnear : 3 / (a₀ + (T - t ^ 2)) ≤ B := by
      change 3 / (a₀ + (T - t ^ 2)) ≤ 3 / (a₀ + T / 2)
      apply (div_le_div_iff₀ htimeDen hden).mpr
      linarith
    constructor
    · exact (show -(3 / a₀) ≤ -3 / (a₀ + (T - t ^ 2)) by
        simpa only [neg_div] using neg_le_neg hglobal).trans hR
    · exact (show -B ≤ -3 / (a₀ + (T - t ^ 2)) by
        simpa only [neg_div] using neg_le_neg hnear).trans hR
  have hB : B ≤ 3 / r ^ 2 := by
    change 3 / (a₀ + T / 2) ≤ 3 / r ^ 2
    apply (div_le_div_iff₀ hden hr2).mpr
    nlinarith
  have hmul : B * v ^ 3 ≤ (3 / r ^ 2) * v ^ 3 :=
    mul_le_mul_of_nonneg_right hB (pow_nonneg hv 3)
  have harith : -2 * v ^ 3 / r ^ 2 ≤ -(2 * B / 3) * (v ^ 3 - 0 ^ 3) := by
    calc
      -2 * v ^ 3 / r ^ 2 = -(2 / 3 : ℝ) * ((3 / r ^ 2) * v ^ 3) := by ring
      _ ≤ -(2 / 3 : ℝ) * (B * v ^ 3) :=
        mul_le_mul_of_nonpos_left hmul (by norm_num)
      _ = -(2 * B / 3) * (v ^ 3 - 0 ^ 3) := by ring
  rw [H.regularizedCost_congr_scalar_lower_bound first last hle T (3 / a₀) B 0 v
    (fun j t ht x => (hfloors j t ht x).1)
    (fun j t ht x => (hfloors j t ht x).2) p q]
  exact (WithTop.coe_le_coe.mpr harith).trans
    (H.regularizedCost_ge first last hle T B 0 v p q)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
