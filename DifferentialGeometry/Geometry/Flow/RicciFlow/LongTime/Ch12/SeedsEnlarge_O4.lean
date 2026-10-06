import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

/-!
# CH12-O4, group G3a: scalar enlargement and Hamilton–Ivey conversion at a seed (D-WBD §4.2–4.3)

Given a parabolic seed `hasSmallParabolicCurvature H u y (a r)` with volume `≥ c₁ (a r)³` on a tower
history at a late time `u`, the profile field `larger_ball_scalar_control` (with
`A = 20 / a + 1 / c₁`) bounds the scalar curvature on `B_u(y, 20 r)` by `K (a r)⁻²`; the
history Hamilton–Ivey pinching (from the cutoff records and the initial identification, base
`a₀ = u`) turns this into `|Rm| ≤ K₀ r⁻²`.  All constants depend only on `a`, `c₁` and the
profile (not on the history index, the time or the point).

This file proves only that step.  The seed itself (KL84.2) and the almost-Euclidean subball
(KL83.1) are frozen, not proved (DELIVERIES CH12-O4).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **G3a.**  A late parabolic seed of radius `a r` and volume ratio `c₁` gives `|Rm| ≤ K₀ r⁻²`
on the concentric ball of radius `20 r` at the same time, uniformly over the tower. -/
theorem enlarged_rm_bound_of_seed_O4 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (u : Icc (0 : ℝ) H.horizon) (y : (H.stageAt u).Carrier) (r : ℝ), 0 < r →
        T₀ ≤ (u : ℝ) → r ≤ ρ₀ * Real.sqrt u →
        GC.LongTime.hasSmallParabolicCurvature H u y (a * r) →
        ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage u) u) y (a * r) →
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u) y (20 * r),
          Real.sqrt (normSq0S (H.stageMetric (H.activeStage u) u) q 4
            (metricRm04At (H.stageMetric (H.activeStage u) u) q)) ≤ K₀ / r ^ 2 := by
  set A : ℝ := 20 / a + 1 / c₁ with hAdef
  have hA : 0 < A := by positivity
  have hA20 : 20 ≤ A * a := by
    have : A * a = 20 + a / c₁ := by rw [hAdef]; field_simp
    rw [this]; have : 0 < a / c₁ := by positivity
    linarith
  have hAc : A⁻¹ ≤ c₁ := by
    have h20 : 0 < 20 / a := by positivity
    have h1 : 1 / c₁ ≤ A := by rw [hAdef]; linarith
    have := inv_anti₀ (by positivity : 0 < 1 / c₁) h1
    simpa [one_div, inv_inv] using this
  obtain ⟨rbar, K, hrbar, hK, hctrl⟩ := Hp.larger_ball_scalar_control A hA
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  set ρ₀ : ℝ := min (rbar / a) (1 / (2 * a)) with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  set K₀ : ℝ := 2 * Real.sqrt 3 * (3 * K / (2 * a ^ 2) + Real.exp 4 * ρ₀ ^ 2) with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  refine ⟨A, ρ₀, K₀, hA, hρ₀pos, hK₀pos, ?_⟩
  intro n H u y r hr hTu hru hseed hvol q hq
  have hupos : 0 < (u : ℝ) := hA.trans_le hTu
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hupos.le
  have har : 0 < a * r := mul_pos ha hr
  -- scale conditions
  have hr1 : a * r ≤ rbar * Real.sqrt u := by
    have h := hru.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsqrt.le)
    have h2 := mul_le_mul_of_nonneg_left h ha.le
    calc a * r ≤ a * (rbar / a * Real.sqrt u) := h2
      _ = rbar * Real.sqrt u := by field_simp
  have hr2 : a * r ≤ Real.sqrt u / 2 := by
    have h := hru.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hsqrt.le)
    have h2 := mul_le_mul_of_nonneg_left h ha.le
    calc a * r ≤ a * (1 / (2 * a) * Real.sqrt u) := h2
      _ = Real.sqrt u / 2 := by field_simp
  have htime : 2 * (a * r) ^ 2 < (u : ℝ) := by
    have h0 : 0 ≤ a * r := har.le
    have : (a * r) ^ 2 ≤ (Real.sqrt u / 2) ^ 2 := pow_le_pow_left₀ h0 hr2 2
    have h4 : (Real.sqrt u / 2) ^ 2 = u / 4 := by rw [div_pow, hsq]; norm_num
    rw [h4] at this
    linarith
  have hacc : ∀ s ∈ Icc ((u : ℝ) / 2) u, δ s < Hp.largerBallAccuracy A s :=
    fun s hs => Hp.largerBallAccuracy_on_late_half_interval hA hTu hs
  have hvol' : ENNReal.ofReal (A⁻¹ * (a * r) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage u) u) y (a * r) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
    exact mul_le_mul_of_nonneg_right hAc (by positivity)
  have hqA : q ∈ riemannianBallOf (H.stageMetric (H.activeStage u) u) y (A * (a * r)) := by
    apply riemannianBallOf_mono _ _ _ hq
    have : 20 * r ≤ A * a * r := mul_le_mul_of_nonneg_right hA20 hr.le
    linarith [mul_assoc A a r]
  have hscal := hctrl n u y (a * r) htime hacc hseed hvol' hr1 q hqA
  -- Hamilton–Ivey on the tower history
  have hpin : InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage u) u) (a₀ + u) q := by
    obtain ⟨hf, hs⟩ := hHI H (F.tower.initial n)
    exact ((H.fixedHamiltonIveyRegion_and_scalar_lower (Hp.records n) ha₀ hf hs).1
      (H.activeStage u) u (H.activeStage_mem u) q).1
  have hbd := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (H.stageMetric (H.activeStage u) u) q
    hupos (by linarith : (u : ℝ) ≤ a₀ + u) hpin hscal
  refine hbd.trans ?_
  set B : ℝ := K * ((a * r) ^ 2)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  have hr2pos : 0 < r ^ 2 := by positivity
  have hexp : Real.exp 4 / u ≤ Real.exp 4 * ρ₀ ^ 2 / r ^ 2 := by
    have hrs : r ^ 2 ≤ ρ₀ ^ 2 * u := by
      have := pow_le_pow_left₀ hr.le hru 2
      rwa [mul_pow, hsq] at this
    rw [div_le_div_iff₀ hupos hr2pos]
    have he : 0 < Real.exp 4 := Real.exp_pos 4
    nlinarith
  have hmax0 : max B 0 = B := max_eq_left hB0
  have hE0 : 0 ≤ Real.exp 4 * ρ₀ ^ 2 / r ^ 2 := by positivity
  have hmax : max B (Real.exp 4 / u) ≤ B + Real.exp 4 * ρ₀ ^ 2 / r ^ 2 :=
    max_le (by linarith) (by linarith)
  have hBeq : B = K / a ^ 2 / r ^ 2 := by rw [hB]; field_simp
  rw [hmax0]
  have h23 : 0 ≤ 2 * Real.sqrt 3 := by positivity
  calc 2 * Real.sqrt 3 * (B / 2 + max B (Real.exp 4 / u))
      ≤ 2 * Real.sqrt 3 * (B / 2 + (B + Real.exp 4 * ρ₀ ^ 2 / r ^ 2)) := by gcongr
    _ = K₀ / r ^ 2 := by rw [hBeq, hK₀]; field_simp; ring

end GC.LongTime.Ch12
