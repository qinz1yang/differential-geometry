import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

namespace DifferentialGeometry

open Set MeasureTheory intervalIntegral
open scoped ContDiff

private theorem exists_smooth_clamp_aux (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
      (∀ t ∈ Set.Icc a b, ψ t = t) ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt ψ 1 t) ∧
      ∀ t : ℝ, ψ t ∈ Set.Icc (a - 1) (b + 1) := by
  classical
  set c : ℝ := (a + b) / 2 with hc
  have hrIn_pos : 0 < (b - a) / 2 := by linarith
  set χb : ContDiffBump c :=
    { rIn := (b - a) / 2
      rOut := (b - a) / 2 + 1
      rIn_pos := hrIn_pos
      rIn_lt_rOut := by linarith } with hχb
  have hrIn_eq : χb.rIn = (b - a) / 2 := rfl
  have hrOut_eq : χb.rOut = (b - a) / 2 + 1 := rfl
  set χ : ℝ → ℝ := fun u => χb u with hχ
  have hχ_cont : Continuous χ := χb.continuous
  have hχ_int : ∀ s t : ℝ, IntervalIntegrable χ volume s t :=
    fun s t => hχ_cont.intervalIntegrable s t
  have h1_int : ∀ s t : ℝ, IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s t :=
    fun s t => continuous_const.intervalIntegrable s t
  have hχ_nonneg : ∀ u : ℝ, 0 ≤ χ u := fun u => χb.nonneg
  have hχ_le_one : ∀ u : ℝ, χ u ≤ 1 := fun u => χb.le_one
  have hχ_one : ∀ u ∈ Set.Icc a b, χ u = 1 := by
    intro u hu
    refine χb.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, hrIn_eq, abs_le, hc]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hχ_zero_right : ∀ u : ℝ, b + 1 ≤ u → χ u = 0 := by
    intro u hu
    have hnot : u ∉ Function.support χ := by
      rw [show Function.support χ = Metric.ball c χb.rOut from χb.support_eq]
      rw [Metric.mem_ball, Real.dist_eq, not_lt, hrOut_eq]
      have h1 : (b - a) / 2 + 1 ≤ u - c := by rw [hc]; linarith
      exact h1.trans (le_abs_self _)
    exact Function.notMem_support.mp hnot
  have hχ_zero_left : ∀ u : ℝ, u ≤ a - 1 → χ u = 0 := by
    intro u hu
    have hnot : u ∉ Function.support χ := by
      rw [show Function.support χ = Metric.ball c χb.rOut from χb.support_eq]
      rw [Metric.mem_ball, Real.dist_eq, not_lt, hrOut_eq]
      have h1 : (b - a) / 2 + 1 ≤ -(u - c) := by rw [hc]; linarith
      exact h1.trans (neg_le_abs _)
    exact Function.notMem_support.mp hnot
  set ψ : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, χ u with hψ
  have hψ_sderiv : ∀ t : ℝ, HasStrictDerivAt ψ (χ t) t :=
    fun t => hχ_cont.integral_hasStrictDerivAt 0 t
  have hψ_diff : Differentiable ℝ ψ :=
    fun t => (hψ_sderiv t).hasDerivAt.differentiableAt
  have hψ_deriv : deriv ψ = χ := funext fun t => (hψ_sderiv t).hasDerivAt.deriv
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    refine contDiff_infty_iff_deriv.mpr ⟨hψ_diff, ?_⟩
    rw [hψ_deriv]
    exact χb.contDiff
  have hψ_id : ∀ t ∈ Set.Icc a b, ψ t = t := by
    intro t ht
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ⟨ha.le, hb.le⟩ ⟨ht.1, ht.2⟩
    have hcongr : Set.EqOn χ (fun _ : ℝ => (1 : ℝ)) (Set.uIcc 0 t) :=
      fun u hu => hχ_one u (hsub hu)
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_congr hcongr]
    simp
  have hψ_le_pos : ∀ t : ℝ, 0 ≤ t → ψ t ≤ t := by
    intro t ht
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ht (hχ_int 0 t) (h1_int 0 t)
      (fun u _ => hχ_le_one u)
    rw [hψ]
    simp only
    calc ∫ u in (0 : ℝ)..t, χ u ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) := hmono
      _ = t := by simp
  have hψ_nonneg_pos : ∀ t : ℝ, 0 ≤ t → 0 ≤ ψ t := by
    intro t ht
    rw [hψ]
    simp only
    exact intervalIntegral.integral_nonneg ht (fun u _ => hχ_nonneg u)
  have hψ_nonpos_neg : ∀ t : ℝ, t ≤ 0 → ψ t ≤ 0 := by
    intro t ht
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_symm]
    have h0 : 0 ≤ ∫ u in t..(0 : ℝ), χ u :=
      intervalIntegral.integral_nonneg ht (fun u _ => hχ_nonneg u)
    linarith
  have hψ_ge_neg : ∀ t : ℝ, t ≤ 0 → t ≤ ψ t := by
    intro t ht
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ht (hχ_int t 0) (h1_int t 0)
      (fun u _ => hχ_le_one u)
    have h1 : (∫ _ in t..(0 : ℝ), (1 : ℝ)) = -t := by simp
    rw [hψ]
    simp only
    rw [intervalIntegral.integral_symm]
    have h2 : (∫ u in t..(0 : ℝ), χ u) ≤ -t := by rw [← h1]; exact hmono
    linarith
  have hψ_ub : ∀ t : ℝ, ψ t ≤ b + 1 := by
    intro t
    by_cases htb : t ≤ b + 1
    · by_cases ht0 : 0 ≤ t
      · exact (hψ_le_pos t ht0).trans htb
      · exact (hψ_nonpos_neg t (not_le.mp ht0).le).trans (by linarith)
    · push Not at htb
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hχ_int 0 (b + 1)) (hχ_int (b + 1) t)
      have hzero : (∫ u in (b + 1)..t, χ u) = 0 := by
        have hcongr : Set.EqOn χ (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (b + 1) t) := by
          intro u hu
          have hmin : b + 1 ≤ u := by
            have := hu.1
            rw [Set.uIcc_of_le htb.le] at hu
            exact hu.1
          exact hχ_zero_right u hmin
        rw [intervalIntegral.integral_congr hcongr]
        simp
      have hval : ψ t = ψ (b + 1) := by
        rw [hψ]
        simp only
        rw [← hadd, hzero, add_zero]
      rw [hval]
      exact hψ_le_pos (b + 1) (by linarith)
  have hψ_lb : ∀ t : ℝ, a - 1 ≤ ψ t := by
    intro t
    by_cases hta : a - 1 ≤ t
    · by_cases ht0 : t ≤ 0
      · exact (hψ_ge_neg t ht0).trans' hta
      · exact (hψ_nonneg_pos t (not_le.mp ht0).le).trans' (by linarith)
    · push Not at hta
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hχ_int 0 (a - 1)) (hχ_int (a - 1) t)
      have hzero : (∫ u in (a - 1)..t, χ u) = 0 := by
        have hcongr : Set.EqOn χ (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (a - 1) t) := by
          intro u hu
          have hmax : u ≤ a - 1 := by
            rw [Set.uIcc_of_ge hta.le] at hu
            exact hu.2
          exact hχ_zero_left u hmax
        rw [intervalIntegral.integral_congr hcongr]
        simp
      have hval : ψ t = ψ (a - 1) := by
        rw [hψ]
        simp only
        rw [← hadd, hzero, add_zero]
      rw [hval]
      exact hψ_ge_neg (a - 1) (by linarith)
  refine ⟨ψ, hψ_smooth, hψ_id, ?_, fun t => ⟨hψ_lb t, hψ_ub t⟩⟩
  intro t ht
  simpa only [hχ_one t ht] using (hψ_sderiv t).hasDerivAt

theorem exists_smooth_clamp (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t ∈ Set.Icc a b, ψ t = t) ∧
      ∀ t : ℝ, |ψ t| ≤ b - a + 2 := by
  obtain ⟨ψ, hψ, hψid, _hψderiv, hψrange⟩ := exists_smooth_clamp_aux a b ha hb
  refine ⟨ψ, hψ, hψid, fun t => ?_⟩
  rw [abs_le]
  exact ⟨by linarith [(hψrange t).1], by linarith [(hψrange t).2]⟩

theorem exists_smooth_time_clamp
    (A D margin : ℝ) (hAD : A < D) (hmargin : 0 < margin) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      (∀ t ∈ Set.Icc A D, ρ t = t) ∧
      (∀ t ∈ Set.Icc A D, HasDerivAt ρ 1 t) ∧
      ∀ t : ℝ, ρ t ∈ Set.Icc (A - margin) (D + margin) := by
  let center := (A + D) / 2
  let a := (A - center) / margin
  let b := (D - center) / margin
  have ha : a < 0 := div_neg_of_neg_of_pos (by dsimp only [a, center]; linarith) hmargin
  have hb : 0 < b := div_pos (by dsimp only [b, center]; linarith) hmargin
  obtain ⟨ψ, hψ, hψid, hψderiv, hψrange⟩ := exists_smooth_clamp_aux a b ha hb
  let inner : ℝ → ℝ := fun t => (t - center) / margin
  let ρ : ℝ → ℝ := fun t => center + margin * ψ (inner t)
  have hinner : ContDiff ℝ ∞ inner :=
    (contDiff_id.sub contDiff_const).div_const margin
  have hρ : ContDiff ℝ ∞ ρ := by
    exact contDiff_const.add (contDiff_const.mul (hψ.comp hinner))
  have hinnerMem : ∀ t ∈ Set.Icc A D, inner t ∈ Set.Icc a b := by
    intro t ht
    constructor
    · dsimp only [inner, a]
      exact (div_le_div_iff_of_pos_right hmargin).2
        (sub_le_sub_right ht.1 center)
    · dsimp only [inner, b]
      exact (div_le_div_iff_of_pos_right hmargin).2
        (sub_le_sub_right ht.2 center)
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro t ht
    dsimp only [ρ]
    rw [show ψ (inner t) = inner t from hψid (inner t) (hinnerMem t ht)]
    dsimp only [inner]
    field_simp [hmargin.ne']
    ring
  · intro t ht
    have hinnerDeriv : HasDerivAt inner (1 / margin) t := by
      simpa only [one_div] using ((hasDerivAt_id t).sub_const center).div_const margin
    have hcomp := (hψderiv (inner t) (hinnerMem t ht)).comp t hinnerDeriv
    have hscaled := hcomp.const_mul margin
    have htotal := (hasDerivAt_const t center).add hscaled
    have htotal' : HasDerivAt ρ (0 + margin * (1 * (1 / margin))) t := by
      simpa only [ρ, Function.comp_apply] using htotal
    have hcoefficient : 0 + margin * (1 * (1 / margin)) = 1 := by
      field_simp [hmargin.ne']
      ring
    simpa only [hcoefficient] using htotal'
  · intro t
    have hrange := hψrange (inner t)
    constructor
    · have hmul := mul_le_mul_of_nonneg_left hrange.1 hmargin.le
      change A - margin ≤ center + margin * ψ (inner t)
      calc
        A - margin = center + margin * (a - 1) := by
          dsimp only [a]
          field_simp [hmargin.ne']
          ring
        _ ≤ center + margin * ψ (inner t) := by
          simpa only [add_comm] using add_le_add_left hmul center
    · have hmul := mul_le_mul_of_nonneg_left hrange.2 hmargin.le
      change center + margin * ψ (inner t) ≤ D + margin
      calc
        center + margin * ψ (inner t) ≤ center + margin * (b + 1) :=
          by simpa only [add_comm] using add_le_add_left hmul center
        _ = D + margin := by
          dsimp only [b]
          field_simp [hmargin.ne']
          ring

theorem exists_smooth_positive_clamp
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧
      (∀ t ∈ Set.Icc a b, rho t = t) ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt rho 1 t) ∧
      (∀ t : ℝ, 0 < rho t) ∧
      ∀ t : ℝ, rho t ∈ Set.Icc (a / 2) (b + a / 2) := by
  have hmargin : 0 < a / 2 := by linarith
  obtain ⟨rho, hrho, hrho_id, hrho_deriv, hrho_range⟩ :=
    exists_smooth_time_clamp a b (a / 2) hab hmargin
  refine ⟨rho, hrho, hrho_id, hrho_deriv, ?_, ?_⟩
  · intro t
    linarith [(hrho_range t).1]
  · intro t
    have ht := hrho_range t
    constructor <;> linarith [ht.1, ht.2]

theorem eventuallyEq_comp_of_eqOn_Icc_of_mem_Ioo
    {X : Type*} [TopologicalSpace X]
    {rho : ℝ → ℝ} {u : X → ℝ} {a b : ℝ} {x : X}
    (hrho : Set.EqOn rho id (Set.Icc a b))
    (hu : ContinuousAt u x) (hx : u x ∈ Set.Ioo a b) :
    (rho ∘ u) =ᶠ[nhds x] u := by
  filter_upwards [hu (isOpen_Ioo.mem_nhds hx)] with y hy
  simpa only [Function.comp_apply, id_eq] using hrho ⟨hy.1.le, hy.2.le⟩

theorem exists_smooth_positive_clamp_eventuallyEq_on_compact
    {X : Type*} [TopologicalSpace X]
    {K : Set X} {u : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hu : Continuous u) (hpos : ∀ x ∈ K, 0 < u x) :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧
      (∀ t : ℝ, 0 < rho t) ∧
      (∀ x ∈ K, (rho ∘ u) =ᶠ[nhds x] u) := by
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isMinOn hKne hu.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hKne hu.continuousOn
  let a := u xmin / 2
  let b := u xmax + a
  have ha : 0 < a := by
    dsimp [a]
    linarith [hpos xmin hxmin]
  have hab : a < b := by
    dsimp [b]
    linarith [hpos xmax hxmax]
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_pos, _hrho_range⟩ :=
    exists_smooth_positive_clamp a b ha hab
  refine ⟨rho, hrho, hrho_pos, ?_⟩
  intro x hx
  have hminx : u xmin ≤ u x := hmin hx
  have hmaxx : u x ≤ u xmax := hmax hx
  apply eventuallyEq_comp_of_eqOn_Icc_of_mem_Ioo hrho_id hu.continuousAt
  constructor
  · change u xmin / 2 < u x
    linarith [hpos xmin hxmin, hminx]
  · change u x < u xmax + u xmin / 2
    linarith [hpos xmin hxmin, hmaxx]

end DifferentialGeometry
