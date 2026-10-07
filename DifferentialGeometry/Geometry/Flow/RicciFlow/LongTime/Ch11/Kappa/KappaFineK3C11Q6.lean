import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFinePackC11Q6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleC11Q4b

/-!
# K3 的 R1 供给：窗口常数版 producer + 块对角支配（O-CH11-FINEPACK G2a，后缀 `_C11Q6`）

FINECAP 的 R1 producer `surgeryActionBarrier_of_fineReal_C11Q5` 把请求固定成 `t` 的函数
`fineKappaConsts(…, Eb t, r₀ t, qcan t, ρbar t, t)`；R1 outer 的 fine records 只按**块**支配请求，窗口
`[t/2, t)` 里的 event 可来自相邻两块，所以请求要按窗口选（G0 设计"K3 的窗口统一性"）。

* `surgeryActionBarrier_of_windowConsts_C11Q6`：每个 `(A, n, t)`（带 accuracy guard）给一组输入
  `(E, Aact, r₀, qcan, ρ)`（`√(t/2) ≤ E`、`Λ A · E ≤ Aact`、`r₀ ≤ nr t/100`、`nr(t)⁻² ≤ qcan`）与
  窗口 event 的
  neck / δ / fine realization（对 `fineBarrierConsts_C11Q5` 在这组输入处的值）⇒ `SurgeryActionBarrier_C11Q`。
  证明 = FINECAP producer，只把常数换成逐窗口的。
* `k3BlockConsts_C11Q6 m rad`：块 `m` 的最坏输入（astra `preparedSpatialPhysicalQualityRequest` 同口径：
  `E = √(3^m)`、作用量 `Λ(12·3^m)·E`、`r₀ = rad/100`、`qcan = rad⁻²`、`ρ = 1`）处的 K3 常数。
* `k3Window_of_blocks_C11Q6`：逐 event 的块数据 `hev`（raw caps 定理 block / m-i 子句的合取形：块时刻
  `b_m < s ≤ 3^m`、`δ(s) ≤ cap m`、`[s, 2s]` 上 `rad(m+1) ≤ nr`、A-guard `A < 12·3^m`、fine tuple 上的
  raw cap）
  + 块请求支配 `hdom`（块 `m` 的 fine tuple 支配 `k3BlockConsts m` 与 `k3BlockConsts (m−1)`）⇒ 上一条的窗口
  前提。窗口常数取窗口内**最小块** `m₀` 的 `k3BlockConsts m₀ (rad (m₀+1))`：`t ≤ 2 s₀ ≤ 2·3^{m₀}` 给 `E`，
  m-i 子句给 `rad(m₀+1) ≤ nr t`，窗口 event 只来自块 `m₀, m₀+1`。
* `surgeryActionBarrier_of_blocks_C11Q6`：合成；
  `Λ = weightedMinLevel_C11Q2 (cutoffBarrierConst_C11Q3 ∘ max · 1)`
  （KAPPA3 nodesScaled 端到端的同一水平），`α = diagonalAccuracy_C11S q.delta`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. level 单调 -/

/-- κ 线作用量水平 `Λ(A) = e^{C(max A 1)/2 + 32/√2} + 1` 单调。 -/
theorem kappaLevel_mono_C11Q6 {A A' : ℝ} (h : A ≤ A') :
    weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A ≤
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A' := by
  have hC := cutoffBarrierConst_mono_C11Q6 (A := max A 1) (A' := max A' 1)
    (le_max_of_le_right zero_le_one) (max_le_max h le_rfl)
  have hexp := Real.exp_le_exp.mpr (by linarith :
    cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2 ≤
      cutoffBarrierConst_C11Q3 (max A' 1) / 2 + 32 / Real.sqrt 2)
  change Real.exp (cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2) + 1 ≤
    Real.exp (cutoffBarrierConst_C11Q3 (max A' 1) / 2 + 32 / Real.sqrt 2) + 1
  linarith

/-! ## 2. 窗口常数版 K3 producer -/

/-- **K3（窗口常数版）**：每个 `(A, n, t)`（带 guard）有输入 `(E, Aact, r₀, qcan, ρ)` 使窗口 `[t/2, t]` 内
event 的 neck ≤ ρ、`δ ≤ c.1`，`[t/2, t)` 内的 static cap 在
`c = fineBarrierConsts(E, Aact, r₀, qcan, Λrec, ρ)`
上有 fine realization ⇒ `SurgeryActionBarrier_C11Q`。 -/
theorem surgeryActionBarrier_of_windowConsts_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {Λ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hΛ : ∀ A, 0 < A → 0 < Λ A)
    (hwin : ∀ A, 0 < A → ∀ n (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon),
      0 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
      ∃ E Aact r₀ qcan ρ : ℝ, Real.sqrt ((t : ℝ) / 2) ≤ E ∧ Λ A * E ≤ Aact ∧ 0 < r₀ ∧
        r₀ ≤ N.params.neckRadius t / 100 ∧ (N.params.neckRadius t ^ 2)⁻¹ ≤ qcan ∧ 0 < ρ ∧
        (∀ j : Fin (F.tower.history n).toHistory.eventCount,
          (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ →
          (F.tower.history n).toHistory.time j.succ ≤ t →
          N.params.neckRadius ((F.tower.history n).toHistory.time j.succ) ≤ ρ ∧
          N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).1) ∧
        ∀ (i : Fin (F.tower.history n).toHistory.eventCount) b,
          (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time i.succ →
          (F.tower.history n).toHistory.time i.succ < t →
          FineCapRealization_C11Q5 ((N.records n i).static b)
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.2.1
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.2.2
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.1) :
    SurgeryActionBarrier_C11Q F δ α N.params.neckRadius Λ := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball Bf hBf v hv
  have hr0 : 0 < r := hsmall.1
  have ht0 : 0 < (t : ℝ) := by nlinarith
  have hid : Nonempty (InitialIdentification P g R.toHistory) := ⟨F.tower.initial n⟩
  obtain ⟨hv2, -, hsq, hvE, hslice⟩ := halfClock_slice_facts_C11Q2 R hr hb hv
  refine ⟨?_, fun _ => cutoffValue_attained_C11Q2 R hid (N.records n) hBf hbt seedTrace x hr0
    hv.1 hv2 hr hslice⟩
  intro q hq
  have hW := hwin A hA n t ht0 hacc
  obtain ⟨E, Aact, r₀, qcan, ρ, hE, hAact, hr₀, hr₀nr, hqcan, hρ, hev, hreal⟩ := hW
  have hE0 : 0 ≤ E := (Real.sqrt_nonneg _).trans hE
  have hnrt : 0 < N.params.neckRadius t := N.params.neckRadius_pos _ t.2.1
  have hqcan0 : 0 < qcan := lt_of_lt_of_le (inv_pos.mpr (pow_pos hnrt 2)) hqcan
  have hE2 : (t : ℝ) - Real.sqrt ((t : ℝ) / 2) ^ 2 = (t : ℝ) / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hball' : H.isParabolicallyRmControlledBall t x r₀ :=
    ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀ (hr₀nr.trans hϱ₀)
  have hrt : r ≤ Real.sqrt ((t : ℝ) / 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  refine fineWindowBarrier_slice_C11Q5 (A := Aact) R hid N.params (N.records n) N.Ctime hE0 hr₀
    hqcan0 hρ t (Real.sqrt ((t : ℝ) / 2)) hE ?_ ?_ ?_ ?_ x hball' hBf _ q ?_ ?_
  · intro j hj1 hj2
    rw [hE2] at hj1
    exact (hev j hj1 hj2).2
  · intro j hj1 hj2
    rw [hE2] at hj1
    exact (hev j hj1 hj2).1
  · intro j y _ s hs hst hqs
    have hs0 : 0 ≤ s := ((F.tower.history n).toHistory.time_nonneg j).trans hs.1.le
    refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hqs)
    refine le_trans ?_ hqcan
    have hle : N.params.neckRadius t ≤ N.params.neckRadius s :=
      N.radius_antitone (show s ∈ Ici (0 : ℝ) from hs0) (show (t : ℝ) ∈ Ici (0 : ℝ) from t.2.1)
        hst.le
    exact inv_anti₀ (pow_pos hnrt 2) (pow_le_pow_left₀ hnrt.le hle 2)
  · intro i b hi1 hi2
    rw [hE2] at hi1
    exact hreal i b hi1 hi2
  · rw [hsq]
    exact hvE
  · refine lt_of_le_of_lt hq (WithTop.coe_lt_coe.mpr ?_)
    have hΛA := hΛ A hA
    have hrE : r ≤ E := hrt.trans hE
    nlinarith [mul_le_mul_of_nonneg_left hrE hΛA.le]

/-! ## 3. 块常数与块对角支配 -/

/-- 块 `m` 的 K3 常数：最坏输入 `E = √(3^m)`、`Aact = Λ(12·3^m)·E`、`r₀ = rad/100`、`qcan = rad⁻²`、`ρ = 1`
（`rad` = 下一块半径 `rad(m+1)`，lookahead 先定）。 -/
def k3BlockConsts_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Λrec : ℝ)
    (Ctime : ℝ≥0) (m : ℕ) (rad : ℝ) : ℝ × ℝ × ℝ × ℕ :=
  fineBarrierConsts_C11Q5 P₀ g₀ (Real.sqrt ((3 : ℝ) ^ m))
    (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (12 * (3 : ℝ) ^ m) *
      Real.sqrt ((3 : ℝ) ^ m)) (rad / 100) ((rad ^ 2)⁻¹) Λrec 1 Ctime

/-- 块时刻骨架：`b_{m'} < s ≤ t ≤ 2·3^{m₀}` ⇒ `m' ≤ m₀ + 1`。 -/
theorem block_le_succ_of_time_C11Q6 {m₀ m' : ℕ} {s : ℝ}
    (hlo : preparedSpatialHorizon m' < s) (hs : s ≤ 2 * (3 : ℝ) ^ m₀) : m' ≤ m₀ + 1 := by
  by_contra hcon
  obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
  have hk : m₀ + 1 ≤ k := by omega
  have hpow : (3 : ℝ) ^ (m₀ + 1) ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h3 : (0 : ℝ) < 3 ^ m₀ := pow_pos (by norm_num) m₀
  change (3 : ℝ) ^ k < s at hlo
  rw [pow_succ] at hpow
  linarith

/-- **块对角支配 ⇒ 窗口常数**（`surgeryActionBarrier_of_windowConsts_C11Q6` 的 `hwin`）。`hev`：塔 event 的块数据
（raw caps 定理 block / m-i 子句的合取形）；`hdom`：块 `m` 与 `m+1` 的 fine tuple 都支配 `k3BlockConsts m`。 -/
theorem k3Window_of_blocks_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdom : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) :
    ∀ A, 0 < A → ∀ n (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon),
      0 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t,
        N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
      ∃ E Aact r₀ qcan ρ : ℝ, Real.sqrt ((t : ℝ) / 2) ≤ E ∧
        weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A * E ≤ Aact ∧
        0 < r₀ ∧ r₀ ≤ N.params.neckRadius t / 100 ∧ (N.params.neckRadius t ^ 2)⁻¹ ≤ qcan ∧
        0 < ρ ∧
        (∀ j : Fin (F.tower.history n).toHistory.eventCount,
          (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ →
          (F.tower.history n).toHistory.time j.succ ≤ t →
          N.params.neckRadius ((F.tower.history n).toHistory.time j.succ) ≤ ρ ∧
          N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).1) ∧
        ∀ (i : Fin (F.tower.history n).toHistory.eventCount) b,
          (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time i.succ →
          (F.tower.history n).toHistory.time i.succ < t →
          FineCapRealization_C11Q5 ((N.records n i).static b)
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.2.1
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.2.2
            (fineBarrierConsts_C11Q5 P g E Aact r₀ qcan N.params.recenterConstant ρ
              N.Ctime).2.1 := by
  classical
  intro A hA n t ht hguard
  have hev' := hev n
  choose blk hblk using hev'
  by_cases hex : ∃ j : Fin (F.tower.history n).toHistory.eventCount,
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ ∧
        (F.tower.history n).toHistory.time j.succ ≤ t
  · have hP : ∃ m, ∃ j : Fin (F.tower.history n).toHistory.eventCount,
        ((t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ ∧
          (F.tower.history n).toHistory.time j.succ ≤ t) ∧ blk j = m := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨blk j, j, hj, rfl⟩
    have hspec := Nat.find_spec hP
    obtain ⟨j₀, hj₀, hbj₀⟩ := hspec
    set m₀ := Nat.find hP with hm₀
    have hmin : ∀ j : Fin (F.tower.history n).toHistory.eventCount,
        ((t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ ∧
          (F.tower.history n).toHistory.time j.succ ≤ t) → m₀ ≤ blk j :=
      fun j hj => Nat.find_min' hP ⟨j, hj, rfl⟩
    have hb₀ := hblk j₀
    rw [hbj₀] at hb₀
    obtain ⟨-, hhi₀, -, hnr₀, hA₀, -⟩ := hb₀
    have ht2 : (t : ℝ) ≤ 2 * (F.tower.history n).toHistory.time j₀.succ := by linarith [hj₀.1]
    have hAm : A < 12 * (3 : ℝ) ^ m₀ := hA₀ A hA (hguard _ ⟨hj₀.1, hj₀.2⟩)
    have hradt : rad (m₀ + 1) ≤ N.params.neckRadius t := hnr₀ t ⟨hj₀.2, ht2⟩
    have hr := hrad (m₀ + 1)
    have hΛrec : 0 < N.params.recenterConstant :=
      lt_of_lt_of_le (by norm_num) N.params.recenterConstant_ge_four
    have hcR := (fineBarrierConsts_spec_C11Q5 P g (E := Real.sqrt ((3 : ℝ) ^ m₀))
      (A := weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))
        (12 * (3 : ℝ) ^ m₀) * Real.sqrt ((3 : ℝ) ^ m₀)) (r₀ := rad (m₀ + 1) / 100)
      (qcan := (rad (m₀ + 1) ^ 2)⁻¹) (Λ := N.params.recenterConstant) (ρ := 1)
      N.Ctime (Real.sqrt_nonneg _) (div_pos hr (by norm_num)) (inv_pos.mpr (pow_pos hr 2))
      hΛrec one_pos).2.2.1
    have hblock : ∀ j : Fin (F.tower.history n).toHistory.eventCount,
        ((t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j.succ ∧
          (F.tower.history n).toHistory.time j.succ ≤ t) → blk j = m₀ ∨ blk j = m₀ + 1 := by
      intro j hj
      have h1 := hmin j hj
      have h2 : blk j ≤ m₀ + 1 :=
        block_le_succ_of_time_C11Q6 (hblk j).1 (hj.2.trans (ht2.trans (by linarith [hhi₀])))
      omega
    refine ⟨Real.sqrt ((3 : ℝ) ^ m₀),
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) (12 * (3 : ℝ) ^ m₀) *
        Real.sqrt ((3 : ℝ) ^ m₀), rad (m₀ + 1) / 100, (rad (m₀ + 1) ^ 2)⁻¹, 1,
      Real.sqrt_le_sqrt (by linarith [hj₀.1]),
      mul_le_mul_of_nonneg_right (kappaLevel_mono_C11Q6 hAm.le) (Real.sqrt_nonneg _),
      div_pos hr (by norm_num), by linarith,
      inv_anti₀ (pow_pos hr 2) (pow_le_pow_left₀ hr.le hradt 2), one_pos, ?_, ?_⟩
    · intro j hj1 hj2
      refine ⟨hnr1 _ ((F.tower.history n).toHistory.time_nonneg _), ?_⟩
      have hδj := (hblk j).2.2.1
      rcases hblock j ⟨hj1, hj2⟩ with h | h
      · rw [h] at hδj
        exact hδj.trans (hdom m₀).2.2.2.1
      · rw [h] at hδj
        exact hδj.trans (hdom m₀).2.2.2.2.2.2.2
    · intro i b hi1 hi2
      have hraw := (hblk i).2.2.2.2.2 b
      have hd := hdom m₀
      rcases hblock i ⟨hi1, hi2.le⟩ with h | h
      · rw [h] at hraw
        obtain ⟨raw, hcan, hsc, hcap⟩ := hraw
        exact fineCapRealization_of_raw_C11Q6 _ raw hcan hsc hcap hcR hd.1 hd.2.1 hd.2.2.1
      · rw [h] at hraw
        obtain ⟨raw, hcan, hsc, hcap⟩ := hraw
        exact fineCapRealization_of_raw_C11Q6 _ raw hcan hsc hcap hcR hd.2.2.2.2.1
          hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.1
  · have hnrt : 0 < N.params.neckRadius t := N.params.neckRadius_pos _ t.2.1
    refine ⟨Real.sqrt ((t : ℝ) / 2),
      weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A *
        Real.sqrt ((t : ℝ) / 2), N.params.neckRadius t / 100, (N.params.neckRadius t ^ 2)⁻¹, 1,
      le_rfl, le_rfl, div_pos hnrt (by norm_num), le_rfl, le_rfl, one_pos, ?_, ?_⟩
    · intro j hj1 hj2
      exact absurd ⟨j, hj1, hj2⟩ hex
    · intro i b hi1 hi2
      exact absurd ⟨i, hi1, hi2.le⟩ hex

/-- **K3 由块数据（R1）**：`hev` + `hdom` + `nr ≤ 1` ⇒ `SurgeryActionBarrier_C11Q` 于
`δ = q.delta`、`α = diagonalAccuracy_C11S q.delta`、`Λ = weightedMinLevel_C11Q2 (C ∘ max · 1)`。
**无** `hact`、
**无** `hfine`（δ 条件已被块 cap `cap m ≤ c.1` 支付）。 -/
theorem surgeryActionBarrier_of_blocks_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdom : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1) :
    SurgeryActionBarrier_C11Q F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) :=
  surgeryActionBarrier_of_windowConsts_C11Q6 N
    (fun A _ => weightedMinLevel_pos_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)) A)
    (k3Window_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdom)

end GC.LongTime.Ch11
