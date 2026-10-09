import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TraceFamily_CX12

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- On a fixed finite initial time interval, a sufficiently small normalized
radius lies below the profile's neck radius. Antitonicity supplies the
positive scale floor needed for the bad-configuration selection. -/
theorem radius_le_neck_on_bounded_time_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {b r t U : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (htU : t ≤ U)
    (hscale : r ≤ b * Real.sqrt t) (hcap : b * Real.sqrt U ≤ Hp.parameters.neckRadius U) :
    r ≤ Hp.parameters.neckRadius t := by
  calc r ≤ b * Real.sqrt t := hscale
    _ ≤ b * Real.sqrt U := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htU) hb
    _ ≤ Hp.parameters.neckRadius U := hcap
    _ ≤ Hp.parameters.neckRadius t := Hp.radius_antitone ht (ht.trans htU) htU

/-- The cutoff requirement for a restarted subball is discharged at its
own time, when its radius is a fixed fraction of the neck scale there. -/
theorem eventually_recent_nominal_below_neck_fraction_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {C θ : ℝ} (hC : 0 < C) (hθ : 0 < θ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∀ r : ℝ,
      θ * Hp.parameters.neckRadius t ≤ r →
      ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, C * (Hp.records n i).nominalRadius h ≤ r := by
  obtain ⟨T, hT, hrecent⟩ := Hp.recent_cutoff_smallness (θ / C) (div_pos hθ hC)
  refine ⟨T, hT, fun t ht r hr n i hi h => ?_⟩
  have hm := mul_le_mul_of_nonneg_left (hrecent t ht n i hi h) hC.le
  calc C * (Hp.records n i).nominalRadius h
      ≤ C * (θ / C * Hp.parameters.neckRadius t) := hm
    _ = θ * Hp.parameters.neckRadius t := by field_simp
    _ ≤ r := hr

/-- Time and normalized-radius slack for a smaller ball at an earlier
time. This is used after choosing the bad time beyond twice the initial
threshold. -/
theorem earlier_smaller_normalized_radius_CX12 {b r q t v : ℝ}
    (hb : 0 ≤ b) (hq : 0 ≤ q) (ht : 0 ≤ t) (hv : 0 ≤ v) (htv : t / 2 ≤ v)
    (hr : r ≤ b * Real.sqrt t) (hqr : q ≤ r / 2) :
    q ≤ b * Real.sqrt v := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  rw [mul_pow, Real.sq_sqrt ht] at hr2
  have hq2 := pow_le_pow_left₀ hq hqr 2
  rw [div_pow] at hq2
  have hbt : b ^ 2 * t ≤ b ^ 2 * (2 * v) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg b)
  have hsqrt : (b * Real.sqrt v) ^ 2 = b ^ 2 * v := by rw [mul_pow, Real.sq_sqrt hv]
  have hpos : 0 ≤ b * Real.sqrt v := mul_nonneg hb (Real.sqrt_nonneg _)
  nlinarith [mul_nonneg (sq_nonneg b) hv]

end GC.LongTime.Ch12
