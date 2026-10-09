import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedWinBlockC11SW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedWindowCXCW

/-!
# hseedWin 的序列级 producer 与 selection 适配（O-CH11-SEEDWIN-P G2，后缀 `_C11SW`）

`hseedWin(n)` 只依赖 seed `(t_n, r_n)`；P6SEL selector 不动 seed 窗（design-C11-seedwin-producer §1）。
本文件给出的生产路径：
* `eventually_native_le_of_ceiling_C11SW` / `eventually_native_le_of_scalarSq_C11SW`：坏点 ceiling
  `R ≤ nr(t)⁻²` + `r√R/200 → ∞`（或 `R r² → ∞`）⇒ 最终 `nr(t) ≤ r`（`ratio_of_selection_C11Q4b` 的同一论证，
  不要求 `∀ n, 0 < r n`）；
* `eventually_seedWin_of_fresh_C11SW`：band 常值 + `nr(t) ≤ r` + `hfresh`（只约束 crossing 支：
  `t − r²/2 ≤ a_k < t ⇒ nr a_k ≤ r`）⇒ hseedWin；
* `eventually_seedWin_of_large_C11SW` / `eventually_seedWin_of_rbar_C11SW`：`r ≥ 1`（hband 的
  `r̄√t < r` + `t → ∞`）+ `nr ≤ 1` ⇒ hseedWin，**无任何 seed-window 前提**；
* `exists_subseq_seedWin_or_eventually_fresh_C11SW`：子列上逐 n hseedWin，或最终 fresh-activation；
* `seedWin_of_badSeed_C11SW`：坏 seed（`¬Good` at `t`）经 `badPoint_scalar_le_native_CXCW` 的 ceiling
  + `R(x) r² → ∞`（P6SEL 唯一发散前提）+ `hfresh` ⇒ hseedWin（selection 之前即成立）；
* `leftShift_selection_data_C11SW`：CX-STAGE left shift 后，ceiling / `hradii` / κ 线窗口三项仍成立。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. `nr(t) ≤ r` 的两个来源 -/

/-- **ceiling + `hradii` ⇒ 最终 `nr(t) ≤ r`**（`ratio_of_selection_C11Q4b` 的论证，`r` 正性由发散给出）。 -/
theorem eventually_native_le_of_ceiling_C11SW {nr : ℝ → ℝ} {t r R : ℕ → ℝ}
    (hpos : ∀ n, 0 < nr (t n)) (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) :
    ∀ᶠ n in atTop, nr (t n) ≤ r n := by
  filter_upwards [hradii.eventually_ge_atTop 1] with n hn
  have hnr := hpos n
  have hs : Real.sqrt (R n) ≤ (nr (t n))⁻¹ := by
    calc Real.sqrt (R n) ≤ Real.sqrt ((nr (t n) ^ 2)⁻¹) := Real.sqrt_le_sqrt (hRle n)
      _ = (nr (t n))⁻¹ := by rw [Real.sqrt_inv, Real.sqrt_sq hnr.le]
  have hr : 0 < r n := by
    by_contra hneg
    have h0 : r n / 200 * Real.sqrt (R n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [le_of_not_gt hneg]) (Real.sqrt_nonneg _)
    linarith
  have h1 : 1 ≤ r n / 200 * (nr (t n))⁻¹ :=
    hn.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h2 : nr (t n) ≤ r n / 200 := by
    calc nr (t n) = nr (t n) * 1 := (mul_one _).symm
      _ ≤ nr (t n) * (r n / 200 * (nr (t n))⁻¹) := mul_le_mul_of_nonneg_left h1 hnr.le
      _ = r n / 200 := by field_simp
  linarith

/-- **ceiling + `R r² → ∞` ⇒ 最终 `nr(t) ≤ r`**（P6SEL 的唯一发散前提形，`r > 0`）。 -/
theorem eventually_native_le_of_scalarSq_C11SW {nr : ℝ → ℝ} {t r R : ℕ → ℝ}
    (hpos : ∀ n, 0 < nr (t n)) (hr : ∀ n, 0 < r n) (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹)
    (hdiv : Tendsto (fun n => R n * r n ^ 2) atTop atTop) :
    ∀ᶠ n in atTop, nr (t n) ≤ r n := by
  filter_upwards [hdiv.eventually_ge_atTop 1] with n hn
  have hnr := hpos n
  have hrn := hr n
  have h1 : 1 ≤ (nr (t n) ^ 2)⁻¹ * r n ^ 2 :=
    hn.trans (mul_le_mul_of_nonneg_right (hRle n) (sq_nonneg _))
  rw [inv_mul_eq_div, one_le_div (by positivity)] at h1
  nlinarith

/-! ## 2. hseedWin 的 producer -/

/-- **fresh 形 producer**：band 常值 + `t → ∞` + `2r² < t` + 最终 `nr(t) ≤ r` + `hfresh`（crossing 支
的旧块半径 `nr a_k ≤ r`）⇒ hseedWin。同块支由 band 常值支付。 -/
theorem eventually_seedWin_of_fresh_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℕ → ℝ} (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n)
    (hle : ∀ᶠ n in atTop, nr (t n) ≤ r n)
    (hfresh : ∀ᶠ n in atTop, ∀ k : ℕ, t n - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
      (5 / 6 : ℝ) * 3 ^ k < t n → nr ((5 / 6 : ℝ) * 3 ^ k) ≤ r n) :
    ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n := by
  filter_upwards [hlate.eventually_gt_atTop (5 / 2), hle, hfresh] with n h1 h2 h3
  rcases seedWin_or_fresh_C11SW hconst (htime n) h1 h2 with h | ⟨k, hk1, hk2, hk3⟩
  · exact h
  · exact absurd (h3 k hk1 hk2) (not_le.mpr hk3)

/-- **大尺度 producer**：`nr ≤ 1` 于 `Ici 0` + `2r² < t` + 最终 `1 ≤ r` ⇒ hseedWin（无 seed-window 前提）。 -/
theorem eventually_seedWin_of_large_C11SW {nr : ℝ → ℝ} (hnr1 : ∀ s, 0 ≤ s → nr s ≤ 1)
    {t r : ℕ → ℝ} (htime : ∀ n, 2 * r n ^ 2 < t n) (hlarge : ∀ᶠ n in atTop, 1 ≤ r n) :
    ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n := by
  filter_upwards [hlarge] with n hn
  have h0 : 0 ≤ t n - r n ^ 2 / 2 := by nlinarith [htime n, sq_nonneg (r n)]
  exact (hnr1 _ h0).trans hn

/-- hband 的 `r̄√t < r` + `t → ∞` ⇒ 最终 `1 ≤ r`。 -/
theorem eventually_one_le_of_rbar_C11SW {t r : ℕ → ℝ} {rbar : ℝ} (hrbar : 0 < rbar)
    (hband : ∀ n, rbar * Real.sqrt (t n) < r n) (hlate : Tendsto t atTop atTop) :
    ∀ᶠ n in atTop, 1 ≤ r n := by
  filter_upwards [hlate.eventually_ge_atTop (rbar⁻¹ ^ 2)] with n hn
  have hs : rbar⁻¹ ≤ Real.sqrt (t n) := by
    calc rbar⁻¹ = Real.sqrt (rbar⁻¹ ^ 2) := (Real.sqrt_sq (inv_pos.mpr hrbar).le).symm
      _ ≤ Real.sqrt (t n) := Real.sqrt_le_sqrt hn
  have h1 : 1 ≤ rbar * Real.sqrt (t n) := by
    calc (1 : ℝ) = rbar * rbar⁻¹ := (mul_inv_cancel₀ hrbar.ne').symm
      _ ≤ rbar * Real.sqrt (t n) := mul_le_mul_of_nonneg_left hs hrbar.le
  linarith [hband n]

/-- **hband 路线 producer**：`r̄√t < r`、`t → ∞`、`nr ≤ 1` ⇒ hseedWin（免费）。 -/
theorem eventually_seedWin_of_rbar_C11SW {nr : ℝ → ℝ} (hnr1 : ∀ s, 0 ≤ s → nr s ≤ 1)
    {t r : ℕ → ℝ} {rbar : ℝ} (hrbar : 0 < rbar) (hband : ∀ n, rbar * Real.sqrt (t n) < r n)
    (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n) :
    ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n :=
  eventually_seedWin_of_large_C11SW hnr1 htime (eventually_one_le_of_rbar_C11SW hrbar hband hlate)

/-- **子列二分**：或沿严格单调子列逐 n hseedWin，或最终 fresh-activation
（`t − r²/2 ≤ a_k < t`、`nr t ≤ r < nr a_k`）。 -/
theorem exists_subseq_seedWin_or_eventually_fresh_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r : ℕ → ℝ} (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n)
    (hle : ∀ᶠ n in atTop, nr (t n) ≤ r n) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, nr (t (φ n) - r (φ n) ^ 2 / 2) ≤ r (φ n)) ∨
      ∀ᶠ n in atTop, ∃ k : ℕ, t n - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k ∧
        (5 / 6 : ℝ) * 3 ^ k < t n ∧ nr (t n) ≤ r n ∧ r n < nr ((5 / 6 : ℝ) * 3 ^ k) := by
  by_cases hfreq : ∃ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n
  · exact Or.inl (extraction_of_frequently_atTop hfreq)
  · right
    rw [not_frequently] at hfreq
    filter_upwards [hfreq, hlate.eventually_gt_atTop (5 / 2), hle] with n hn h1 h2
    rcases seedWin_or_fresh_C11SW hconst (htime n) h1 h2 with h | ⟨k, hk1, hk2, hk3⟩
    · exact absurd h hn
    · exact ⟨k, hk1, hk2, h2, hk3⟩

/-! ## 3. 坏 seed 直接生产（selection 之前） -/

/-- **坏 seed ⇒ hseedWin**：`(t_n, x_n)` 处 `¬Good`（P6SEL 的 `hbad`）经 `badPoint_scalar_le_native_CXCW`
（`v = T = t_n`）给 ceiling；`R(x) r² → ∞` ⇒ 最终 `nr(t) ≤ r`；band 常值 + `hfresh` ⇒ hseedWin。 -/
theorem seedWin_of_badSeed_C11SW {Kh : ℕ → ObservedHistory.{u}} (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
        ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z, W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun s => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) s) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    {c : ℕ → ℝ} (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
      q.neckRadius w = c k)
    (t : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (x : ∀ n, ((Kh n).stageAt (t n)).Carrier)
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (t n) (x n))
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n))
      (t n)) (x n) * r n ^ 2) atTop atTop)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hfresh : ∀ᶠ n in atTop, ∀ k : ℕ, (t n : ℝ) - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
      (5 / 6 : ℝ) * 3 ^ k < (t n : ℝ) → q.neckRadius ((5 / 6 : ℝ) * 3 ^ k) ≤ r n) :
    ∀ᶠ n in atTop, q.neckRadius ((t n : ℝ) - r n ^ 2 / 2) ≤ r n := by
  have hceil : ∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (t n)) (t n)) (x n) ≤
      (q.neckRadius (t n) ^ 2)⁻¹ := fun n =>
    badPoint_scalar_le_native_CXCW (Kh n) q hC1 hC2 hCtime hanti (hcanonical n) (hderivative n)
      (t n) (t n) le_rfl (x n) (hbad n)
  have hle := eventually_native_le_of_scalarSq_C11SW (t := fun n => (t n : ℝ))
    (fun n => q.neckRadius_pos _ (t n).2.1) hr hceil hdiv
  exact eventually_seedWin_of_fresh_C11SW hconst hlate htime hle hfresh

/-! ## 4. left shift（CX-STAGE）后 CXCW 坏点前提的保持 -/

/-- 单点窗口：window-room `t − r²/2 ≤ σ − L²/R`、`σ − σ' ≤ L²/(2R)`、`R/2 ≤ R'`、`4T ≤ L²` ⇒
`t − r²/2 ≤ σ' − T/R'`。 -/
theorem leftShift_window_C11SW {t r σ σ' R R' L T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (hroom : t - r ^ 2 / 2 ≤ σ - L ^ 2 / R) (hshift : σ - σ' ≤ L ^ 2 / (2 * R))
    (hRR : R / 2 ≤ R') (hL : 4 * T ≤ L ^ 2) :
    t - r ^ 2 / 2 ≤ σ' - T / R' := by
  have hR' : 0 < R' := by linarith
  have h1 : T / R' ≤ 2 * T / R := by
    rw [div_le_div_iff₀ hR' hR]
    nlinarith
  have h2 : 2 * T / R ≤ L ^ 2 / (2 * R) := by
    rw [div_le_div_iff₀ hR (by positivity)]
    nlinarith
  have h3 : L ^ 2 / R / 2 = L ^ 2 / (2 * R) := by ring
  linarith

/-- `R/2 ≤ R'` 下 `r√R/200 → ∞` ⇒ `r√R'/200 → ∞`。 -/
theorem leftShift_radii_C11SW {r R R' : ℕ → ℝ} (hR : ∀ n, 0 < R n) (hRR : ∀ n, R n / 2 ≤ R' n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) :
    Tendsto (fun n => r n / 200 * Real.sqrt (R' n)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (hradii.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hradii.eventually_ge_atTop 0] with n hn
  have hRn := hR n
  have hsq : Real.sqrt (R n) / 2 ≤ Real.sqrt (R' n) := by
    have h4 : (Real.sqrt (R n) / 2) * (Real.sqrt (R n) / 2) = R n / 4 := by
      rw [show (Real.sqrt (R n) / 2) * (Real.sqrt (R n) / 2) =
        (Real.sqrt (R n) * Real.sqrt (R n)) / 4 by ring, Real.mul_self_sqrt hRn.le]
    calc Real.sqrt (R n) / 2 = Real.sqrt ((Real.sqrt (R n) / 2) * (Real.sqrt (R n) / 2)) :=
          (Real.sqrt_mul_self (by positivity)).symm
      _ ≤ Real.sqrt (R' n) := by
          rw [h4]
          exact Real.sqrt_le_sqrt (by linarith [hRR n])
  have hr : 0 ≤ r n := by
    by_contra hneg
    have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRn
    have : r n / 200 * Real.sqrt (R n) < 0 :=
      mul_neg_of_neg_of_pos (by linarith [lt_of_not_ge hneg]) hs
    linarith
  calc r n / 200 * Real.sqrt (R n) / 2 = r n / 200 * (Real.sqrt (R n) / 2) := by ring
    _ ≤ r n / 200 * Real.sqrt (R' n) := mul_le_mul_of_nonneg_left hsq (by positivity)

/-- **left shift 后的 CXCW 坏点前提**：CX-STAGE 的 shifted 坏点 `(σ'_n, z_n)`（`¬Good`、`σ' ≤ t`、
`R/2 ≤ R'`、`σ − σ' ≤ L²/(2R)`）+ 原 selection 的 window-room 与 `hradii` ⇒ ceiling
`R' ≤ nr(t)⁻²`（`badPoint_scalar_le_native_CXCW`，不用 doubling / hseedWin）、`r√R'/200 → ∞`、
κ 线窗口 `∀ T > 0, ∀ᶠ n, t − r²/2 ≤ σ' − T/R'`。seed `(t, r)` 不变，故 hseedWin 不变。 -/
theorem leftShift_selection_data_C11SW {Kh : ℕ → ObservedHistory.{u}} (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
        ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z, W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun s => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) s) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (t σ' : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσt : ∀ n, σ' n ≤ t n)
    (z : ∀ n, ((Kh n).stageAt (σ' n)).Carrier)
    (hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ' n) (z n))
    {r σ R L : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (hRR : ∀ n, R n / 2 ≤
      metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ' n)) (σ' n)) (z n))
    (hshift : ∀ n, σ n - σ' n ≤ L n ^ 2 / (2 * R n))
    (hroom : ∀ n, (t n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hL : Tendsto L atTop atTop)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop) :
    (∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ' n)) (σ' n)) (z n) ≤
      (q.neckRadius (t n) ^ 2)⁻¹) ∧
    Tendsto (fun n => r n / 200 * Real.sqrt
      (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ' n)) (σ' n)) (z n)))
      atTop atTop ∧
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (σ' n : ℝ) - T /
      metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ' n)) (σ' n)) (z n) := by
  refine ⟨fun n => badPoint_scalar_le_native_CXCW (Kh n) q hC1 hC2 hCtime hanti (hcanonical n)
    (hderivative n) (t n) (σ' n) (hσt n) (z n) (hbad n), leftShift_radii_C11SW hR hRR hradii, ?_⟩
  intro T hT
  filter_upwards [hL.eventually_ge_atTop (max 1 (4 * T))] with n hn
  have h1 : 1 ≤ L n := (le_max_left _ _).trans hn
  have h2 : 4 * T ≤ L n := (le_max_right _ _).trans hn
  exact leftShift_window_C11SW (hR n) hT.le (hroom n) (hshift n) (hRR n) (by nlinarith)

/-! ## 5. consumer：替换 CXCW 的 `hsame` -/

/-- **selection ratio + seed-window（`hsame` → band 常值 + `hfresh`）**：CXCW
`selection_ratio_seedWindow_CXCW` 的 `hsame`（两端 native radius 相等）换成树内 band 常值与只约束
crossing 支的 `hfresh`；ceiling `hRle` 同时喂 `ratio_of_selection_C11Q4b` 与 hseedWin。 -/
theorem selection_ratio_seedWin_C11SW {nr : ℝ → ℝ} {c : ℕ → ℝ}
    (hconst : ∀ k w, (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) → nr w = c k)
    {t r R : ℕ → ℝ} (hnr : ∀ n, 0 < nr (t n)) (hr : ∀ n, 0 < r n)
    (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹)
    (hdiv : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hlate : Tendsto t atTop atTop) (htime : ∀ n, 2 * r n ^ 2 < t n)
    (hfresh : ∀ᶠ n in atTop, ∀ k : ℕ, t n - r n ^ 2 / 2 ≤ (5 / 6 : ℝ) * 3 ^ k →
      (5 / 6 : ℝ) * 3 ^ k < t n → nr ((5 / 6 : ℝ) * 3 ^ k) ≤ r n) :
    Tendsto (fun n => r n / nr (t n)) atTop atTop ∧
      ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n :=
  ⟨ratio_of_selection_C11Q4b hnr hr hRle hdiv, eventually_seedWin_of_fresh_C11SW hconst hlate
    htime (eventually_native_le_of_ceiling_C11SW hnr hRle hdiv) hfresh⟩

end GC.LongTime.Ch11
