import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierC1DV
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# G3-alt′（S-A10-DERIV，Route W 的 HG14 入口）：off-countable 变体

`A : ℝ → ℝ`、可数集 `E`（surgery event 时刻）：

* (i) `A ≥ 0`（`Ici T` 上）；
* (ii) `hleft`：处处乘法 left-lsc（`A t ≤ exp ε · A s`，`s ↑ t`）；
* (iii) `hright`：`E` 的点上乘法 right-usc（`A s ≤ exp ε · A t`，`s ↓ t`）；
* (iv) `hbar`：`Ici T \ E` 上 C¹ barrier（G3alt 的 `∃ U B d` 形状，`d < 3A/(4(t+c)) − π`）

⇒ `False`。陈述冻结于 `docs/geometrization/chapter8/design-IFACE-K-transport-20261006.md` §A.4。
证明：`Ψ t = A t/(t+c) + b log (t+c)`，先证通用比较原理
`le_initial_of_left_lsc_off_countable_DV`（比较函数
`f a + ε (t - a) + ε ∑_{e n < t} 2^{-n}`，上确界点用 left-lsc 闭合，`E` 之外用支撑函数导数 `≤ 0`
越过，`E` 的点用 right-usc 越过，跳跃被权重 `ε 2^{-n}` 吸收），再套 `Ψ`。
没有新 def / structure / 具名 Prop。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 权重函数 `W t = ∑' n, [e n < t] (1/2)^n` 的基本性质：非负、`≤ 2`、单调、
以及在 `e n` 之后跳过 `(1/2)^n`。 -/
theorem exists_countable_weight_DV (e : ℕ → ℝ) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧ (∀ t, W t ≤ 2) ∧ Monotone W ∧
      ∀ (n : ℕ) (t s : ℝ), t ≤ e n → e n < s → W t + (1 / 2 : ℝ) ^ n ≤ W s := by
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hw : Summable w := summable_geometric_two
  have hw0 : ∀ n, 0 ≤ w n := fun n => by positivity
  let ind : ℝ → ℕ → ℝ := fun t n => if e n < t then w n else 0
  have hind0 : ∀ t n, 0 ≤ ind t n := fun t n => by
    by_cases h : e n < t <;> simp [ind, h, hw0]
  have hindle : ∀ t n, ind t n ≤ w n := fun t n => by
    by_cases h : e n < t <;> simp [ind, h, hw0]
  have hsumm : ∀ t, Summable (ind t) := fun t =>
    Summable.of_nonneg_of_le (hind0 t) (hindle t) hw
  refine ⟨fun t => ∑' n, ind t n, fun t => tsum_nonneg (hind0 t), fun t => ?_, ?_, ?_⟩
  · calc ∑' n, ind t n ≤ ∑' n, w n := (hsumm t).tsum_le_tsum (hindle t) hw
      _ = 2 := tsum_geometric_two
  · intro s t hst
    refine (hsumm s).tsum_le_tsum (fun n => ?_) (hsumm t)
    by_cases h : e n < s
    · simp [ind, h, lt_of_lt_of_le h hst]
    · simp only [ind, h, ite_false]
      exact hind0 t n
  · intro n t s hts hs
    have hsing : Summable (fun k => if k = n then w n else 0) :=
      (hasSum_ite_eq n (w n)).summable
    have h1 : (∑' k, ind t k) + w n = ∑' k, (ind t k + if k = n then w n else 0) := by
      rw [(hsumm t).tsum_add hsing, tsum_ite_eq]
    rw [h1]
    refine ((hsumm t).add hsing).tsum_le_tsum (fun k => ?_) (hsumm s)
    by_cases hk : k = n
    · subst hk
      have : ¬ e k < t := not_lt.mpr hts
      simp [ind, this, hs]
    · simp only [ind, hk, ite_false, add_zero]
      by_cases h : e k < t
      · simp [h, lt_of_lt_of_le h (hts.trans hs.le)]
      · simp only [h, ite_false]
        exact hind0 s k

/-- 比较原理（左 lsc + 右 usc 于可数集 + 其余点上支撑函数）：
`f` 在 `[a, ∞)` 上满足 (i) 左半连续（只在 `f s ≤ M` 的点上要求）；(ii) 在可数集 `E` 的点右上半连续；
(iii) `E` 之外每点有右上支撑函数且其导数 `≤ 0` ⇒ `f t ≤ f a`（`t ≥ a`）。 -/
theorem le_initial_of_left_lsc_off_countable_DV
    {f : ℝ → ℝ} {a : ℝ} {E : Set ℝ} (hE : E.Countable)
    (hleft : ∀ t : ℝ, a < t → ∀ M η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, a ≤ s → t - δ < s → s < t → f s ≤ M → f t ≤ f s + η)
    (hright : ∀ t ∈ E, a ≤ t → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, t < s → s < t + δ → f s ≤ f t + η)
    (hsupp : ∀ t : ℝ, a ≤ t → t ∉ E → ∃ (φ : ℝ → ℝ) (d : ℝ),
      φ t = f t ∧ f ≤ᶠ[𝓝[>] t] φ ∧ HasDerivAt φ d t ∧ d ≤ 0) :
    ∀ t : ℝ, a ≤ t → f t ≤ f a := by
  obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.mp hE
  obtain ⟨W, hW0, hW2, hWm, hWj⟩ := exists_countable_weight_DV e
  intro b hb
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hba : 0 ≤ b - a := sub_nonneg.mpr hb
  let ε : ℝ := η / (b - a + 3)
  have hε : 0 < ε := div_pos hη (by linarith)
  let g : ℝ → ℝ := fun s => f a + ε * (s - a) + ε * W s
  have hgm : ∀ s t : ℝ, s ≤ t → g s ≤ g t := fun s t hst => by
    have := hWm hst
    dsimp only [g]
    nlinarith
  -- `S'`：到 `t` 为止都被 `g` 控制
  let S : Set ℝ := {t | a ≤ t ∧ t ≤ b ∧ ∀ s : ℝ, a ≤ s → s ≤ t → f s ≤ g s}
  have haS : a ∈ S := ⟨le_rfl, hb, fun s has hsa => by
    have : s = a := le_antisymm hsa has
    subst this
    dsimp only [g]
    nlinarith [hW0 s]⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨b, fun t ht => ht.2.1⟩
  let ts := sSup S
  have hts_le : ts ≤ b := csSup_le hSne fun t ht => ht.2.1
  have hats : a ≤ ts := le_csSup hSbdd haS
  -- Claim A: `ts ∈ S`
  have hlt : ∀ s : ℝ, a ≤ s → s < ts → f s ≤ g s := by
    intro s has hs
    obtain ⟨t', ht', hst'⟩ := exists_lt_of_lt_csSup hSne hs
    exact ht'.2.2 s has hst'.le
  have hA : f ts ≤ g ts := by
    rcases hats.eq_or_lt with h | h
    · rw [← h]
      dsimp only [g]
      nlinarith [hW0 a]
    · refine le_of_forall_pos_le_add fun θ hθ => ?_
      obtain ⟨δ, hδ, hδs⟩ := hleft ts h (g ts) θ hθ
      obtain ⟨s, hs1, hs2⟩ := exists_between (show max a (ts - δ) < ts from
        max_lt h (by linarith))
      have has : a ≤ s := (le_max_left _ _).trans hs1.le
      have hsd : ts - δ < s := (le_max_right _ _).trans_lt hs1
      have h1 := hlt s has hs2
      have h2 := hgm s ts hs2.le
      have := hδs s has hsd hs2 (h1.trans h2)
      linarith
  have htsS : ts ∈ S := ⟨hats, hts_le, fun s has hs => by
    rcases hs.eq_or_lt with h | h
    · rw [h]; exact hA
    · exact hlt s has h⟩
  -- Claim B: `ts = b`
  have hB : ts = b := by
    by_contra hne
    have hlt_b : ts < b := lt_of_le_of_ne hts_le hne
    -- 在 `ts` 右侧有一个开区间使得 `f ≤ g`
    have hright_ex : ∃ u : ℝ, ts < u ∧ ∀ s : ℝ, ts < s → s < u → f s ≤ g s := by
      by_cases hmem : ts ∈ E
      · obtain ⟨n, hn⟩ := he hmem
        have hwn : 0 < (1 / 2 : ℝ) ^ n := by positivity
        obtain ⟨δ, hδ, hδs⟩ := hright ts hmem hats (ε * (1 / 2 : ℝ) ^ n) (by positivity)
        refine ⟨ts + δ, by linarith, fun s hs1 hs2 => ?_⟩
        have h1 := hδs s hs1 hs2
        have h2 := hWj n ts s (le_of_eq hn.symm) (by rw [hn]; exact hs1)
        dsimp only [g]
        nlinarith [hA, show g ts = f a + ε * (ts - a) + ε * W ts from rfl]
      · obtain ⟨φ, d, hφ, hup, hder, hd⟩ := hsupp ts hats hmem
        have hlo := (hasDerivAt_iff_isLittleO.mp hder).def (show 0 < ε / 2 by linarith)
        have hev : ∀ᶠ s in 𝓝[>] ts, ts < s ∧ f s ≤ g s := by
          filter_upwards [nhdsWithin_le_nhds hlo, hup, self_mem_nhdsWithin] with s hs1 hs2 hs3
          have hts' : ts < s := hs3
          rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul,
            abs_of_pos (sub_pos.mpr hts')] at hs1
          have h1 := (abs_le.mp hs1).2
          have h2 := hWm hts'.le
          refine ⟨hts', ?_⟩
          dsimp only [g] at hA ⊢
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hd (sub_nonneg.mpr hts'.le)]
        obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
        exact ⟨u, hu, fun s hs1 hs2 => (hus ⟨hs1, hs2⟩).2⟩
    obtain ⟨u, hu, hus⟩ := hright_ex
    let y := min b ((ts + u) / 2)
    have hy1 : ts < y := lt_min hlt_b (by linarith)
    have hyS : y ∈ S := by
      refine ⟨hats.trans hy1.le, min_le_left _ _, fun s has hsy => ?_⟩
      by_cases hsts : s ≤ ts
      · exact htsS.2.2 s has hsts
      · have h1 : ts < s := not_le.mp hsts
        have h2 : s < u := lt_of_le_of_lt hsy (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        exact hus s h1 h2
    exact absurd (le_csSup hSbdd hyS) (not_le.mpr hy1)
  have := htsS.2.2 b hb (le_of_eq hB.symm)
  have hgb : g b ≤ f a + ε * (b - a) + ε * 2 := by
    dsimp only [g]
    nlinarith [hW2 b]
  have hε2 : ε * (b - a) + ε * 2 ≤ η := by
    have : ε * (b - a + 3) = η := by dsimp only [ε]; field_simp
    nlinarith
  linarith

/-- 辅助：对 `K ≥ 0`、`η > 0`，存在 `ε > 0` 使 `2 * ((exp ε - 1) * K) ≤ η`。 -/
theorem exists_exp_sub_one_mul_le_DV {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ((Real.exp ε - 1) * K) ≤ η := by
  have hq : 0 < η / (2 * (K + 1)) := by positivity
  refine ⟨Real.log (1 + η / (2 * (K + 1))), Real.log_pos (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  have h : η / (2 * (K + 1)) * K ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- 辅助（纯实数算术，无除法）：barrier 比较中单步的不等式。 -/
theorem aux_step_ineq_DV {x y K E lt ls b r η : ℝ} (hE : 1 ≤ E) (hxy : x ≤ E * y) (hyK : y ≤ K)
    (hεK : 2 * ((E - 1) * K) ≤ η) (hlog : lt - ls ≤ r) (hb : 0 < b) (hbr : 2 * (b * r) = η) :
    x + b * lt ≤ y + b * ls + η := by
  have h1 : (E - 1) * y ≤ (E - 1) * K := mul_le_mul_of_nonneg_left hyK (by linarith)
  have h2 : b * (lt - ls) ≤ b * r := mul_le_mul_of_nonneg_left hlog hb.le
  nlinarith

/-- 辅助：`log y - log x ≤ (y - x) / x`（`x, y > 0`）。 -/
theorem log_sub_log_le_div_DV {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have h2 : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- G3-alt′ 主定理（一般 `k ≤ 1`、`b > 0`）。 -/
theorem not_nonnegative_of_C1_majorants_off_countable_div_time_DV
    (A : ℝ → ℝ) (T c k b : ℝ) (E : Set ℝ) (hE : E.Countable) (hT : 0 < T + c)
    (hk : k ≤ 1) (hb : 0 < b) (hn : ∀ t ∈ Ici T, 0 ≤ A t)
    (hleft : ∀ t ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Ici T, t - δ < s → s < t → A t ≤ Real.exp ε * A s)
    (hright : ∀ t ∈ Ici T ∩ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s, t < s → s < t + δ → A s ≤ Real.exp ε * A t)
    (hbar : ∀ t ∈ Ici T \ E, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen U ∧ t ∈ U ∧
      HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
      d < k * A t / (t + c) - b) : False := by
  let F : ℝ → ℝ := fun t => A t / (t + c) + b * Real.log (t + c)
  have hpos (t : ℝ) (ht : T ≤ t) : 0 < t + c := by linarith
  have hlogT (s : ℝ) (hs : T ≤ s) : Real.log (T + c) ≤ Real.log (s + c) :=
    Real.log_le_log hT (by linarith)
  -- 支撑函数
  have hsupp : ∀ t : ℝ, T ≤ t → t ∉ E → ∃ (φ : ℝ → ℝ) (d : ℝ),
      φ t = F t ∧ F ≤ᶠ[𝓝[>] t] φ ∧ HasDerivAt φ d t ∧ d ≤ 0 := by
    intro t ht htE
    obtain ⟨U, B, dB, hU, htU, hdB, heq, hupper, hder⟩ := hbar t ⟨ht, htE⟩
    have hdtime : HasDerivAt (fun z : ℝ => z + c) 1 t := (hasDerivAt_id t).add_const c
    have hdlog : HasDerivAt (fun z : ℝ => Real.log (z + c)) (1 / (t + c)) t := by
      simpa only [mul_one, one_div, Function.comp_def] using
        (Real.hasDerivAt_log (hpos t ht).ne').comp t hdtime
    let d := (dB * (t + c) - B t) / (t + c) ^ 2 + b * (1 / (t + c))
    refine ⟨fun z => B z / (z + c) + b * Real.log (z + c), d, by simp [F, heq], ?_, ?_, ?_⟩
    · filter_upwards [show U ∈ 𝓝[>] t from nhdsWithin_le_nhds (hU.mem_nhds htU),
        self_mem_nhdsWithin] with z hzU htz
      have hzT : z ∈ Ici T := ht.trans (show t < z from htz).le
      change A z / (z + c) + b * Real.log (z + c) ≤ B z / (z + c) + b * Real.log (z + c)
      exact add_le_add (div_le_div_of_nonneg_right
        (hupper z ⟨hzU, hzT⟩) (hpos z hzT).le) le_rfl
    · convert (hdB.div hdtime (hpos t ht).ne').add (hdlog.const_mul b) using 1
      all_goals first | rfl | simp [d]
    · have hder' : dB * (t + c) < k * A t - b * (t + c) := by
        have h := (lt_div_iff₀ (hpos t ht)).mp (show dB + b < k * A t / (t + c) by linarith)
        nlinarith
      have hcoeff := mul_le_mul_of_nonneg_right hk (hn t ht)
      have hnum : dB * (t + c) - A t + b * (t + c) ≤ 0 := by nlinarith
      have hd : d = (dB * (t + c) - A t + b * (t + c)) / (t + c) ^ 2 := by
        dsimp [d]
        rw [heq]
        field_simp
      rw [hd]
      exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)
  -- 左 lsc（只在 `F s ≤ M` 的点上）
  have hleftF : ∀ t : ℝ, T < t → ∀ M η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, T ≤ s → t - δ < s → s < t → F s ≤ M → F t ≤ F s + η := by
    intro t htT M η hη
    obtain ⟨r, hr, hbr⟩ : ∃ r : ℝ, 0 < r ∧ 2 * (b * r) = η :=
      ⟨η / (2 * b), by positivity, by field_simp⟩
    let K := max (M - b * Real.log (T + c)) 0
    obtain ⟨ε, hε, hεK⟩ :=
      exists_exp_sub_one_mul_le_DV (le_max_right (M - b * Real.log (T + c)) 0) hη
    obtain ⟨δ₁, hδ₁, h1⟩ := hleft t htT.le ε hε
    refine ⟨min δ₁ (r * (T + c)), lt_min hδ₁ (by positivity), ?_⟩
    intro s hTs hsδ hst hM
    have hmin1 := min_le_left δ₁ (r * (T + c))
    have hmin2 := min_le_right δ₁ (r * (T + c))
    have hAt := h1 s hTs (by linarith) hst
    have hsc := hpos s hTs
    have htc := hpos t htT.le
    have hAs := hn s hTs
    have hAsK : A s / (s + c) ≤ K := by
      have h2 := hlogT s hTs
      have h3 : A s / (s + c) + b * Real.log (s + c) ≤ M := hM
      have h4 := mul_le_mul_of_nonneg_left h2 hb.le
      exact (show A s / (s + c) ≤ M - b * Real.log (T + c) by linarith).trans (le_max_left _ _)
    have e1 : A t / (t + c) ≤ Real.exp ε * (A s / (s + c)) := by
      rw [← mul_div_assoc]
      calc A t / (t + c) ≤ Real.exp ε * A s / (t + c) := div_le_div_of_nonneg_right hAt htc.le
        _ ≤ Real.exp ε * A s / (s + c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) hAs) hsc (by linarith)
    have e3 : Real.log (t + c) - Real.log (s + c) ≤ r := by
      have h4 := log_sub_log_le_div_DV hsc htc
      have h5 : (t + c - (s + c)) / (s + c) ≤ (t - s) / (T + c) := by
        rw [show t + c - (s + c) = t - s by ring]
        exact div_le_div_of_nonneg_left (by linarith) hT (by linarith)
      have h6 : (t - s) / (T + c) ≤ r := by
        rw [div_le_iff₀ hT]
        linarith
      linarith
    exact aux_step_ineq_DV (Real.one_le_exp hε.le) e1 hAsK hεK e3 hb hbr
  -- 右 usc（`E` 的点）
  have hrightF : ∀ t ∈ E, T ≤ t → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, t < s → s < t + δ → F s ≤ F t + η := by
    intro t htE htT η hη
    obtain ⟨r, hr, hbr⟩ : ∃ r : ℝ, 0 < r ∧ 2 * (b * r) = η :=
      ⟨η / (2 * b), by positivity, by field_simp⟩
    have htc := hpos t htT
    have hKt : 0 ≤ A t / (t + c) := div_nonneg (hn t htT) htc.le
    obtain ⟨ε, hε, hεK⟩ := exists_exp_sub_one_mul_le_DV hKt hη
    obtain ⟨δ₁, hδ₁, h1⟩ := hright t ⟨htT, htE⟩ ε hε
    refine ⟨min δ₁ (r * (t + c)), lt_min hδ₁ (by positivity), ?_⟩
    intro s hts hsδ
    have hmin1 := min_le_left δ₁ (r * (t + c))
    have hmin2 := min_le_right δ₁ (r * (t + c))
    have hAs := h1 s hts (by linarith)
    have hsc := hpos s (htT.trans hts.le)
    have e1 : A s / (s + c) ≤ Real.exp ε * (A t / (t + c)) := by
      rw [← mul_div_assoc]
      calc A s / (s + c) ≤ Real.exp ε * A t / (s + c) := div_le_div_of_nonneg_right hAs hsc.le
        _ ≤ Real.exp ε * A t / (t + c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) (hn t htT)) htc (by linarith)
    have e3 : Real.log (s + c) - Real.log (t + c) ≤ r := by
      have h4 := log_sub_log_le_div_DV htc hsc
      have h6 : (s + c - (t + c)) / (t + c) ≤ r := by
        rw [div_le_iff₀ htc]
        linarith
      linarith
    exact aux_step_ineq_DV (Real.one_le_exp hε.le) e1 le_rfl hεK e3 hb hbr
  have hbound (t : ℝ) (ht : T ≤ t) : F t ≤ F T :=
    le_initial_of_left_lsc_off_countable_DV hE hleftF hrightF hsupp t ht
  let q := (F T + 1) / b
  let t := Real.exp q + T + |T + c| + 1
  have ht : T ≤ t := by dsimp [t]; linarith [Real.exp_pos q, abs_nonneg (T + c)]
  have hsize : Real.exp q ≤ t + c := by dsimp [t]; linarith [neg_le_abs (T + c)]
  have hlog : q ≤ Real.log (t + c) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos q) hsize
  have hlog' := mul_le_mul_of_nonneg_left hlog hb.le
  have hq : b * q = F T + 1 := by dsimp [q]; field_simp
  rw [hq] at hlog'
  have hnonneg : 0 ≤ A t / (t + c) := div_nonneg (hn t ht) (hpos t ht).le
  have hlast := hbound t ht
  dsimp only [F] at hlast hlog'
  linarith

/-- G3-alt′ 冻结陈述（O-IFACE design §A.4，`pi_shift` 形状）：
`A ≥ 0`、乘法 left-lsc、`E` 上乘法 right-usc、`Ici T \ E` 上 C¹ barrier
（`d < 3A/(4(t+c)) - π`）⇒ `False`。 -/
theorem not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV
    (A : ℝ → ℝ) (T c : ℝ) (E : Set ℝ) (hE : E.Countable) (hT : 0 < T + c)
    (hn : ∀ t ∈ Ici T, 0 ≤ A t)
    (hleft : ∀ t ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Ici T, t - δ < s → s < t → A t ≤ Real.exp ε * A s)
    (hright : ∀ t ∈ Ici T ∩ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s, t < s → s < t + δ → A s ≤ Real.exp ε * A t)
    (hbar : ∀ t ∈ Ici T \ E, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ), IsOpen U ∧ t ∈ U ∧
      HasDerivAt B d t ∧ B t = A t ∧ (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
      d < 3 * A t / (4 * (t + c)) - Real.pi) : False := by
  refine not_nonnegative_of_C1_majorants_off_countable_div_time_DV A T c (3 / 4) Real.pi E hE hT
    (by norm_num) Real.pi_pos hn hleft hright ?_
  intro t ht
  obtain ⟨U, B, d, hU, htU, hB, heq, hle, hd⟩ := hbar t ht
  refine ⟨U, B, d, hU, htU, hB, heq, hle, ?_⟩
  convert hd using 1
  rw [div_mul_eq_div_div]
  ring

/-- 辅助：`ContinuousOn A (Ici T)` 与 `A ≥ 0` ⇒ 乘法 left-lsc（`E = ∅` 时的 `hleft`）。 -/
theorem multiplicative_left_lsc_of_continuousOn_DV {A : ℝ → ℝ} {T : ℝ}
    (hc : ContinuousOn A (Ici T)) (hn : ∀ t ∈ Ici T, 0 ≤ A t) :
    ∀ t ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Ici T, t - δ < s → s < t → A t ≤ Real.exp ε * A s := by
  intro t ht ε hε
  rcases (hn t ht).eq_or_lt with h0 | hpos
  · exact ⟨1, one_pos, fun s hs _ _ => by
      rw [← h0]
      exact mul_nonneg (Real.exp_pos ε).le (hn s hs)⟩
  · have hq : 0 < A t * (1 - Real.exp (-ε)) := mul_pos hpos (by
      have := Real.exp_lt_one_iff.mpr (show -ε < 0 by linarith)
      linarith)
    obtain ⟨δ, hδ, hδs⟩ := Metric.continuousWithinAt_iff.mp (hc t ht) _ hq
    refine ⟨δ, hδ, fun s hs hsδ hst => ?_⟩
    have hd : dist s t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hδs hs hd
    rw [Real.dist_eq, abs_lt] at h1
    have h2 : Real.exp (-ε) * A t ≤ A s := by nlinarith [h1.1]
    have h3 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
    calc A t = Real.exp ε * (Real.exp (-ε) * A t) := by rw [← mul_assoc, h3, one_mul]
      _ ≤ Real.exp ε * A s := mul_le_mul_of_nonneg_left h2 (Real.exp_pos ε).le

/-- Consumer（`E = ∅` 退化）：连续 + C¹ barrier 版 `not_nonnegative_of_C1_majorants_pi_shift_DV`
是 off-countable 版（`E = ∅`）的特例；用 G3-alt′ 重新证明它。 -/
theorem not_nonnegative_of_C1_majorants_pi_shift_via_off_countable_DV
    (A : ℝ → ℝ) (T c : ℝ) (hT : 0 < T + c)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hmaj : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ),
      IsOpen U ∧ t ∈ U ∧ HasDerivAt B d t ∧ B t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
        d < 3 * A t / (4 * (t + c)) - Real.pi) : False :=
  not_nonnegative_of_C1_majorants_off_countable_pi_shift_DV A T c ∅ Set.countable_empty hT
    hnonnegative (multiplicative_left_lsc_of_continuousOn_DV hcontinuous hnonnegative)
    (fun t ht => absurd ht.2 (Set.notMem_empty t)) (fun t ht => hmaj t ht.1)

end DifferentialGeometry.Analysis
