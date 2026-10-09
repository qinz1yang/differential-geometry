import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility

/-!
# CH12-O28 G1: the recent-surgery guard for restarted subballs (KL Lemma 86.2)

`[FROZEN] CH12-O28`.  The recent-surgery guard of `hG2c` / `sub86_3` asks that every event of the
tower with time in `[t / 2, t]` has nominal radius at most `r / C`.  For a subball restarted at an
earlier time `u < t` this half-window guard is not inherited (events in `[u / 2, t / 2)` are not
controlled by it), but the *parabolic window* guard on `[t - Λ r ^ 2, t]` is: a restarted ball
`(u, r')` with `t - Λ r ^ 2 ≤ u - Λ r' ^ 2` has its window inside the old one.  This file proves

* the half-window guard implies the window guard once `Λ r ^ 2 ≤ t / 2`;
* the window guard restarts along the time-plus-radius order;
* the half-window guard holds automatically at scales comparable to the neck radius, late;
* the window guard gives the `hnom` premise of `record_seed_tracedRegion_CX2` on a tower history.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- The half-window guard implies the parabolic-window guard when the window fits in `[t/2, t]`. -/
theorem guardWin_of_guardHalf_O28 (Hp : AnalyticSurgeryProfile F δ) {C Λ t r : ℝ}
    (hwin : Λ * r ^ 2 ≤ t / 2)
    (hguard : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, C * (Hp.records n i).nominalRadius h ≤ r) :
    ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t - Λ * r ^ 2) t →
        ∀ h, C * (Hp.records n i).nominalRadius h ≤ r := by
  intro n i hi h
  exact hguard n i ⟨by linarith [hi.1], hi.2⟩ h

/-- Pointwise rescaling of one guard inequality: `C * ν ≤ r` and `C' * r ≤ C * r'` give
`C' * ν ≤ r'` (for either sign of `ν`). -/
theorem guard_rescale_O28 {C C' r r' ν : ℝ} (hr : 0 < r) (hr' : 0 ≤ r') (hC' : 0 ≤ C')
    (hCC : C' * r ≤ C * r') (hν : C * ν ≤ r) : C' * ν ≤ r' := by
  rcases le_or_gt 0 ν with h0 | h0
  · have h1 : C' * r * ν ≤ C * r' * ν := mul_le_mul_of_nonneg_right hCC h0
    have h2 : C * ν * r' ≤ r * r' := mul_le_mul_of_nonneg_right hν hr'
    have h3 : C' * ν * r ≤ r' * r := by nlinarith
    exact le_of_mul_le_mul_right h3 hr
  · exact (mul_nonpos_of_nonneg_of_nonpos hC' h0.le).trans hr'

/-- The window guard restarts: a ball `(u, r')` that is earlier in the time-plus-radius order
inherits the window guard, with the constant rescaled by `r' / r`. -/
theorem guardWin_restart_O28 (Hp : AnalyticSurgeryProfile F δ) {C C' Λ t u r r' : ℝ}
    (hr : 0 < r) (hr' : 0 ≤ r') (hC' : 0 ≤ C') (hCC : C' * r ≤ C * r') (hut : u ≤ t)
    (hwin : t - Λ * r ^ 2 ≤ u - Λ * r' ^ 2)
    (hguard : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t - Λ * r ^ 2) t →
        ∀ h, C * (Hp.records n i).nominalRadius h ≤ r) :
    ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (u - Λ * r' ^ 2) u →
        ∀ h, C' * (Hp.records n i).nominalRadius h ≤ r' := by
  intro n i hi h
  exact guard_rescale_O28 hr hr' hC' hCC
    (hguard n i ⟨hwin.trans hi.1, hi.2.trans hut⟩ h)

/-- Restart of the `hG2c` guard: the half-window guard at `(t, r0)` with `r0 ≤ b √t` and
`Λ b² ≤ 1/2` gives the window guard at every earlier-smaller ball `(u, r')`. -/
theorem restart_guardWin_O28 (Hp : AnalyticSurgeryProfile F δ) {C₁ C' Λ b t u r0 r' : ℝ}
    (hΛ : 0 ≤ Λ) (ht : 0 ≤ t) (hΛb : Λ * b ^ 2 ≤ 1 / 2) (hr0 : 0 < r0)
    (hr0b : r0 ≤ b * Real.sqrt t) (hr' : 0 ≤ r') (hC' : 0 ≤ C') (hCC : C' * r0 ≤ C₁ * r')
    (hut : u ≤ t) (hwin : t - Λ * r0 ^ 2 ≤ u - Λ * r' ^ 2)
    (hguard : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) :
    ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (u - Λ * r' ^ 2) u →
        ∀ h, C' * (Hp.records n i).nominalRadius h ≤ r' := by
  have hsq : r0 ^ 2 ≤ b ^ 2 * t := by
    have h1 : r0 ^ 2 ≤ (b * Real.sqrt t) ^ 2 := pow_le_pow_left₀ hr0.le hr0b 2
    rwa [mul_pow, Real.sq_sqrt ht] at h1
  have hfit : Λ * r0 ^ 2 ≤ t / 2 := by
    have h2 : Λ * r0 ^ 2 ≤ Λ * (b ^ 2 * t) := mul_le_mul_of_nonneg_left hsq hΛ
    have h3 : Λ * b ^ 2 * t ≤ 1 / 2 * t := mul_le_mul_of_nonneg_right hΛb ht
    nlinarith
  exact guardWin_restart_O28 Hp hr0 hr' hC' hCC hut hwin
    (guardWin_of_guardHalf_O28 Hp hfit hguard)

/-- Late in time, the half-window guard holds at every scale comparable to the neck radius
(from `recent_cutoff_smallness`). -/
theorem guardHalf_of_neck_fraction_O28 (Hp : AnalyticSurgeryProfile F δ) {C θ : ℝ}
    (hC : 0 < C) (hθ : 0 < θ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∀ r : ℝ, θ * Hp.parameters.neckRadius t ≤ r →
      ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, C * (Hp.records n i).nominalRadius h ≤ r := by
  obtain ⟨T, hT, hsmall⟩ := Hp.recent_cutoff_smallness (θ / C) (div_pos hθ hC)
  refine ⟨T, hT, fun t hTt r hr n i hi h => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hsmall t hTt n i hi h) hC.le
  have h2 : C * (θ / C * Hp.parameters.neckRadius t) = θ * Hp.parameters.neckRadius t := by
    field_simp
  linarith

/-- The window guard gives the `hnom` premise of `record_seed_tracedRegion_CX2` on the tower
history `F.tower.history n`, between any two observation times inside the window. -/
theorem hnom_of_guardWin_O28 (Hp : AnalyticSurgeryProfile F δ) (n : ℕ)
    {a v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon} {C Λ t r : ℝ}
    (ha : t - Λ * r ^ 2 ≤ a.val) (hv : v.val ≤ t)
    (hguard : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t - Λ * r ^ 2) t →
        ∀ h, C * (Hp.records n i).nominalRadius h ≤ r) :
    ∀ i : Fin (F.tower.history n).eventCount,
      (F.tower.history n).toHistory.activeStage a ≤ i.castSucc →
        i.succ ≤ (F.tower.history n).toHistory.activeStage v →
          ∀ h, C * (Hp.records n i).nominalRadius h ≤ r := by
  intro j hai hiv h
  refine hguard n j ⟨?_, ?_⟩ h
  · by_contra hlt
    rw [not_le] at hlt
    have hle : j.succ ≤ (F.tower.history n).toHistory.activeStage a :=
      (F.tower.history n).toHistory.le_activeStage a j.succ (by linarith)
    have hlt' : j.castSucc < j.succ := Fin.castSucc_lt_succ
    exact absurd (hai.trans_lt hlt') (not_lt.mpr hle)
  · have h1 : (F.tower.history n).toHistory.time j.succ ≤
        (F.tower.history n).toHistory.time ((F.tower.history n).toHistory.activeStage v) :=
      (F.tower.history n).toHistory.time_strictMono.monotone hiv
    exact h1.trans (((F.tower.history n).toHistory.activeStage_time_le v).trans hv)

end GC.LongTime.Ch12
