import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Euclidean tier of localized distance smoothing (LC28, tier T1)

Pure analysis on a finite-dimensional real normed space `F`, with Lipschitz control measured by an
arbitrary seminorm `N` (in the manifold tier `N` is the norm of the metric at the chart centre).

* `sub_le_mul_sub_of_eventually_increment_le`: a continuous function on `[a, b]` whose right
  increments are eventually bounded by `c (s - t)` for every `c > B` satisfies
  `φ b - φ a ≤ B (b - a)` (one-dimensional Dini comparison).
* `sub_le_seminorm_of_eventually_increment_le`: directional control of a function on a convex set
  (every right difference quotient in direction `w` eventually below any `c > a N w`) implies the
  Lipschitz bound `h y' - h y ≤ a N (y' - y)`.
* `exists_contDiff_seminorm_lipschitz_approx`: mollification preserves an `a`-Lipschitz bound with
  respect to `N` on the `r`-interior of the set and moves values by at most `a · sup_{‖z‖ ≤ r} N z`.
* `exists_contDiff_approx_of_directional_control`: the two combined.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal Convolution

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

/-- One-dimensional Dini comparison: right increments eventually below every slope `c > B`
force the increment over `[a, b]` to be at most `B (b - a)`. -/
theorem sub_le_mul_sub_of_eventually_increment_le {φ : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b))
    (hdini : ∀ t ∈ Ico a b, ∀ c, B < c → ∀ᶠ s in 𝓝[>] t, φ s - φ t ≤ c * (s - t)) :
    φ b - φ a ≤ B * (b - a) := by
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := φ) (a := a) (b := b) hφ
    (B := fun x => φ a + B * (x - a)) (B' := fun _ => B) (by simp)
    (by fun_prop)
    (by
      intro x _
      simpa using ((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul B |>.const_add (φ a))
    (by
      intro x hx r hr
      have hev := hdini x hx ((B + r) / 2) (by linarith)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hxs⟩
      have hpos : 0 < s - x := sub_pos.mpr hxs
      rw [slope_def_field]
      rw [div_lt_iff₀ hpos]
      nlinarith)
    (right_mem_Icc.mpr hab)
  linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Directional control on a convex set gives a one-sided Lipschitz bound for the seminorm `N`. -/
theorem sub_le_seminorm_of_eventually_increment_le (N : Seminorm ℝ F) {S : Set F}
    (hS : Convex ℝ S) {h : F → ℝ} (hh : ContinuousOn h S) {a : ℝ}
    (hdini : ∀ y ∈ S, ∀ w : F, ∀ c, a * N w < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), h (y + t • w) - h y ≤ t * c)
    {y y' : F} (hy : y ∈ S) (hy' : y' ∈ S) :
    h y' - h y ≤ a * N (y' - y) := by
  let φ : ℝ → ℝ := fun t => h (y + t • (y' - y))
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (y' - y) ∈ S := by
    intro t ht
    have := hS.add_smul_sub_mem hy hy' ht
    simpa using this
  have hφ : ContinuousOn φ (Icc 0 1) := by
    refine hh.comp (by fun_prop) ?_
    intro t ht
    exact hseg t ht
  have h1 := sub_le_mul_sub_of_eventually_increment_le (φ := φ) (a := 0) (b := 1)
    (B := a * N (y' - y)) zero_le_one hφ (by
      intro t ht c hc
      have hz := hseg t (Ico_subset_Icc_self ht)
      have hev := hdini (y + t • (y' - y)) hz (y' - y) c hc
      have htend : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
            (continuous_id.sub continuous_const).tendsto t
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact sub_pos.mpr (show t < s from hs)
      filter_upwards [htend.eventually hev] with s hs
      have heq : y + t • (y' - y) + (s - t) • (y' - y) = y + s • (y' - y) := by
        rw [add_assoc, ← add_smul]
        congr 2
        ring
      simp only [φ]
      rw [heq] at hs
      linarith)
  simpa [φ] using h1

/-- Two-sided form of `sub_le_seminorm_of_eventually_increment_le`. -/
theorem abs_sub_le_seminorm_of_eventually_increment_le (N : Seminorm ℝ F) {S : Set F}
    (hS : Convex ℝ S) {h : F → ℝ} (hh : ContinuousOn h S) {a : ℝ}
    (hdini : ∀ y ∈ S, ∀ w : F, ∀ c, a * N w < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), h (y + t • w) - h y ≤ t * c) :
    ∀ y ∈ S, ∀ y' ∈ S, |h y - h y'| ≤ a * N (y - y') := by
  intro y hy y' hy'
  rw [abs_le]
  constructor
  · have := sub_le_seminorm_of_eventually_increment_le N hS hh hdini hy hy'
    rw [map_sub_rev] at this
    linarith
  · exact sub_le_seminorm_of_eventually_increment_le N hS hh hdini hy' hy

variable [FiniteDimensional ℝ F]

/-- Mollification with Lipschitz control for a seminorm. If `h` is `a`-Lipschitz for `N` on `S`
and `N` is bounded by a multiple of the norm, then for every radius `r > 0` there is a smooth `h'`
which is `a`-Lipschitz for `N` between points whose closed `r`-balls lie in `S`, and which differs
from `h` at such points by at most `a δ`, where `δ` bounds `N` on the closed `r`-ball. -/
theorem exists_contDiff_seminorm_lipschitz_approx (N : Seminorm ℝ F) {C : ℝ}
    (hNC : ∀ v, N v ≤ C * ‖v‖) {a : ℝ} (ha : 0 ≤ a) {S : Set F} {h : F → ℝ}
    (hh : ∀ y ∈ S, ∀ y' ∈ S, |h y - h y'| ≤ a * N (y - y')) {r δ : ℝ} (hr : 0 < r)
    (hδ : ∀ z : F, ‖z‖ ≤ r → N z ≤ δ) :
    ∃ h' : F → ℝ, ContDiff ℝ ∞ h' ∧
      (∀ y y', closedBall y r ⊆ S → closedBall y' r ⊆ S → |h' y - h' y'| ≤ a * N (y - y')) ∧
      (∀ y, closedBall y r ⊆ S → |h' y - h y| ≤ a * δ) := by
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := Measure.addHaar
  -- McShane extension in the ambient norm, for local integrability only.
  have hLip : LipschitzOnWith (Real.toNNReal (a * C)) h S := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |h y - h y'| ≤ a * N (y - y') := hh y hy y' hy'
      _ ≤ a * (C * ‖y - y'‖) := mul_le_mul_of_nonneg_left (hNC _) ha
      _ = a * C * ‖y - y'‖ := by ring
      _ ≤ (Real.toNNReal (a * C) : ℝ) * ‖y - y'‖ :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)
  obtain ⟨H, hHlip, hHeq⟩ := hLip.extend_real
  let bump : ContDiffBump (0 : F) := ⟨r / 2, r, by positivity, by linarith⟩
  let ρ : F → ℝ := bump.normed μ
  have hρ_nonneg : ∀ t, 0 ≤ ρ t := fun t => bump.nonneg_normed t
  have hρ_int : ∫ t, ρ t ∂μ = 1 := bump.integral_normed
  have hρ_supp : ∀ t, ρ t ≠ 0 → ‖t‖ < r := by
    intro t ht
    have : t ∈ Function.support ρ := ht
    rw [bump.support_normed_eq] at this
    simpa using this
  have hρ_cont : Continuous ρ := bump.continuous_normed
  have hρ_cs : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have hH_cont : Continuous H := hHlip.continuous
  let h' : F → ℝ := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] H
  have hval : ∀ y, h' y = ∫ t, ρ t * H (y - t) ∂μ := by
    intro y
    simp [h', convolution_def, smul_eq_mul]
  have hint : ∀ (G : F → ℝ), Continuous G → Integrable (fun t => ρ t * G t) μ := by
    intro G hG
    exact (hρ_cont.mul hG).integrable_of_hasCompactSupport (hρ_cs.mul_right)
  have hHy : ∀ y, Continuous fun t => H (y - t) := fun y => hH_cont.comp (by fun_prop)
  refine ⟨h', ?_, ?_, ?_⟩
  · exact hρ_cs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (bump.contDiff_normed) hH_cont.locallyIntegrable
  · intro y y' hyS hy'S
    rw [hval, hval, ← integral_sub (hint _ (hHy y)) (hint _ (hHy y'))]
    have hbound : ∀ t, ‖ρ t * H (y - t) - ρ t * H (y' - t)‖ ≤ ρ t * (a * N (y - y')) := by
      intro t
      by_cases ht : ρ t = 0
      · simp [ht]
      · have htr := hρ_supp t ht
        have hmem : ∀ z, closedBall z r ⊆ S → z - t ∈ S := fun z hz =>
          hz (by rw [mem_closedBall, dist_eq_norm]; simpa using htr.le)
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg t),
          ← hHeq (hmem y hyS), ← hHeq (hmem y' hy'S)]
        refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg t)
        have := hh _ (hmem y hyS) _ (hmem y' hy'S)
        simpa [Real.norm_eq_abs, sub_sub_sub_cancel_right] using this
    calc ‖∫ t, ρ t * H (y - t) - ρ t * H (y' - t) ∂μ‖
        ≤ ∫ t, ρ t * (a * N (y - y')) ∂μ :=
          norm_integral_le_of_norm_le ((hint _ continuous_const))
            (Eventually.of_forall hbound)
      _ = a * N (y - y') := by rw [integral_mul_const, hρ_int, one_mul]
  · intro y hyS
    have hc : (∫ t, ρ t * h y ∂μ) = h y := by rw [integral_mul_const, hρ_int, one_mul]
    rw [hval, ← hc, ← integral_sub (hint _ (hHy y)) (hint _ continuous_const)]
    have hbound : ∀ t, ‖ρ t * H (y - t) - ρ t * h y‖ ≤ ρ t * (a * δ) := by
      intro t
      by_cases ht : ρ t = 0
      · simp [ht]
      · have htr := hρ_supp t ht
        have hmem : y - t ∈ S :=
          hyS (by rw [mem_closedBall, dist_eq_norm]; simpa using htr.le)
        have hyy : y ∈ S := hyS (mem_closedBall_self hr.le)
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ_nonneg t), ← hHeq hmem]
        refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg t)
        calc |h (y - t) - h y| ≤ a * N (y - t - y) := hh _ hmem _ hyy
          _ = a * N t := by rw [sub_sub_cancel_left, map_neg_eq_map]
          _ ≤ a * δ := mul_le_mul_of_nonneg_left (hδ t htr.le) ha
    calc ‖∫ t, ρ t * H (y - t) - ρ t * h y ∂μ‖
        ≤ ∫ t, ρ t * (a * δ) ∂μ :=
          norm_integral_le_of_norm_le ((hint _ continuous_const))
            (Eventually.of_forall hbound)
      _ = a * δ := by rw [integral_mul_const, hρ_int, one_mul]

/-- T1: Euclidean smoothing with directional control. A function on a convex set whose right
difference quotients in every direction `w` are eventually below every `c > a N w` is approximated,
on the `r`-interior, by a smooth function that keeps the same `N`-Lipschitz bound and moves values by
at most `a δ`; the difference of the two is therefore `2a`-Lipschitz for `N` there. -/
theorem exists_contDiff_approx_of_directional_control (N : Seminorm ℝ F) {C : ℝ}
    (hNC : ∀ v, N v ≤ C * ‖v‖) {a : ℝ} (ha : 0 ≤ a) {S : Set F} (hS : Convex ℝ S)
    {h : F → ℝ} (hh : ContinuousOn h S)
    (hdini : ∀ y ∈ S, ∀ w : F, ∀ c, a * N w < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), h (y + t • w) - h y ≤ t * c)
    {r δ : ℝ} (hr : 0 < r) (hδ : ∀ z : F, ‖z‖ ≤ r → N z ≤ δ) :
    ∃ h' : F → ℝ, ContDiff ℝ ∞ h' ∧
      (∀ y y', closedBall y r ⊆ S → closedBall y' r ⊆ S → |h' y - h' y'| ≤ a * N (y - y')) ∧
      (∀ y, closedBall y r ⊆ S → |h' y - h y| ≤ a * δ) ∧
      (∀ y y', closedBall y r ⊆ S → closedBall y' r ⊆ S →
        |(h' y - h y) - (h' y' - h y')| ≤ 2 * a * N (y - y')) := by
  have hlip := abs_sub_le_seminorm_of_eventually_increment_le N hS hh hdini
  obtain ⟨h', hsmooth, hl, hv⟩ := exists_contDiff_seminorm_lipschitz_approx N hNC ha hlip hr hδ
  refine ⟨h', hsmooth, hl, hv, ?_⟩
  intro y y' hy hy'
  have h1 := hl y y' hy hy'
  have h2 := hlip y (hy (mem_closedBall_self hr.le)) y' (hy' (mem_closedBall_self hr.le))
  calc |(h' y - h y) - (h' y' - h y')| = |(h' y - h' y') - (h y - h y')| := by ring_nf
    _ ≤ |h' y - h' y'| + |h y - h y'| := abs_sub _ _
    _ ≤ a * N (y - y') + a * N (y - y') := add_le_add h1 h2
    _ = 2 * a * N (y - y') := by ring

end DifferentialGeometry.Analysis.Calculus
