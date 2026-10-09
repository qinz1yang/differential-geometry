import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutoffThreshold_CX2

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

/-- Uniform choices for the seed window, the G3a scale, and the length
factor. The strict `τ b² < 1/2` is the exact W2 requirement. -/
theorem exists_window_constants_CX2 {c b₀ ρ₀ K : ℝ}
    (hc : 0 < c) (hb₀ : 0 < b₀) (hρ₀ : 0 < ρ₀) (hK : 0 < K) :
    ∃ b τ : ℝ, 0 < b ∧ 0 < τ ∧ b ≤ b₀ ∧ 2 * b ≤ ρ₀ ∧ τ ≤ c ∧
      τ * b ^ 2 < 1 / 2 ∧ Real.exp (9 * K * τ) < 2 := by
  let b := min b₀ (min (ρ₀ / 2) (1 / 2))
  let τ := min c (min 1 (Real.log 2 / (18 * K + 1)))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := lt_min hb₀ (lt_min (by positivity) (by norm_num))
  have hτ : 0 < τ := lt_min hc (lt_min zero_lt_one (by positivity))
  have hb₂ : b ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbρ : b ≤ ρ₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁ : τ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hτlog : τ ≤ Real.log 2 / (18 * K + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨b, τ, hb, hτ, min_le_left _ _, by linarith, min_le_left _ _, ?_, ?_⟩
  · have hbSq : b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hb.le hb₂ 2
    have hprod := mul_le_mul_of_nonneg_right hτ₁ (sq_nonneg b)
    nlinarith
  · have hτbound := (le_div_iff₀ (by positivity : 0 < 18 * K + 1)).mp hτlog
    have hkt : 0 < K * τ := mul_pos hK hτ
    have hexponent : 9 * K * τ < Real.log 2 := by nlinarith
    exact (Real.exp_lt_exp.mpr hexponent).trans_eq (Real.exp_log (by norm_num))

/-- Every time in the short parabolic window is in the late half interval
and meets G3a's original radius constraint. -/
theorem window_time_and_radius_CX2 {b τ ρ₀ t r v : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (hscale : 2 * b ≤ ρ₀)
    (hwindow : τ * b ^ 2 < 1 / 2) (ht : 0 < t) (hr : 0 < r)
    (hrb : r ≤ b * Real.sqrt t) (hv : v ∈ Icc (t - τ * r ^ 2) t) :
    t / 2 < v ∧ 0 < v ∧ r ≤ ρ₀ * Real.sqrt v := by
  have hrs : r ^ 2 ≤ b ^ 2 * t := by
    have h := pow_le_pow_left₀ hr.le hrb 2
    rwa [mul_pow, Real.sq_sqrt ht.le] at h
  have hτrs := mul_le_mul_of_nonneg_left hrs hτ.le
  have htb := mul_lt_mul_of_pos_right hwindow ht
  have hvhalf : t / 2 < v := by nlinarith [hv.1]
  have hvpos : 0 < v := (half_pos ht).trans hvhalf
  have hsqrt : Real.sqrt t ≤ 2 * Real.sqrt v := by
    have htsq := Real.sq_sqrt ht.le
    have hvsq := Real.sq_sqrt hvpos.le
    nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg v]
  refine ⟨hvhalf, hvpos, ?_⟩
  calc
    r ≤ b * Real.sqrt t := hrb
    _ ≤ b * (2 * Real.sqrt v) := mul_le_mul_of_nonneg_left hsqrt hb.le
    _ = (2 * b) * Real.sqrt v := by ring
    _ ≤ ρ₀ * Real.sqrt v := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg v)

/-- The distortion bound leaves room between the transported path and the
20r curvature buffer. -/
theorem six_radius_length_CX2 {K τ r : ℝ} (hr : 0 < r)
    (hτ : Real.exp (9 * K * τ) < 2) :
    3 * r * Real.exp (9 * K * τ) < 6 * r ∧ 6 * r < 20 * r := by
  have h := mul_lt_mul_of_pos_left hτ (by positivity : 0 < 3 * r)
  constructor <;> nlinarith

/-- Increasing the multiplier preserves the seed's exact recent-radius
hypothesis, including its quantification over all tower histories. -/
theorem recent_nominal_mono_CX2
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) {Λ₀ Λ t r : ℝ} (hΛ : Λ₀ ≤ Λ)
    (hrec : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) :
    ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, Λ₀ * (Hp.records n i).nominalRadius h ≤ r := by
  intro n i hi h
  exact (mul_le_mul_of_nonneg_right hΛ ((Hp.records n i).nominal_pos h).le).trans
    (hrec n i hi h)

end GC.LongTime.Ch12
