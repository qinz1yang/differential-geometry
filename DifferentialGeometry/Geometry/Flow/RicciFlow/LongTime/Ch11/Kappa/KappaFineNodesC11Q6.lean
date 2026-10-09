import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineK3C11Q6

/-!
# R1 打包：K3 + event / URE node 数据 + 端到端（O-CH11-FINEPACK G2，后缀 `_C11Q6`）

lead 08:0x：R1 outer 要**同时**供给 K3（替代 `hact + hfine`）与 KAPPA3 的两类 request 形 node 数据
（`EventNodeData_C11Q4`（G6 种子尺度版：只对 `nr t/100 ≤ r` 的种子）、`UREBlockNodeData_C11Q4`），三者共用
translate 保持 / 块对角支配 / 终塔对齐。输入是塔 event 的**块数据** `hev`（astra
`PreparedSpatialChain.exists_surgery_with_retained_raw_caps` 的 block 子句 + m-i 子句的合取形，A-guard 已经
`diagonalLargerBallAccuracy_eq_C11Q6` 换成 κ 线的 `α = diagonalAccuracy_C11S q.delta`）与块请求支配
`hdomK3 / hdomE / hdomU`（C11W 策略 tower 的请求，G1 `tower_of_blockSteps_policy_C11Q6`）。

* node 输入只依赖 event 所在块 `m` 与下一块半径 `rad(m+1)`（与种子无关，lead R-a 裁定）：
  `nodeE = √(3^m)`、`nodeR = rad(m+1)/100`、`nodeQ = rad(m+1)⁻²`、`nodeRho = 1`，
  `nodeA = (E(12·3^m) + 1)·√(3^m)`（event）/ `D(12·3^m)·√(3^m)`（URE）。块请求
  `eventBlockRequest_C11Q6` / `ureBlockRequest_C11Q6` = KAPPA3 的 chooser 在这组输入处的值。
* `eventNodeData_of_blocks_C11Q6`（`nonempty_pre841Data_of_native_nodesScaled_C11Q4` 的 `hnode` 逐字形）、
  `ureNodeData_of_blocks_C11Q6`（`hure` 逐字形）。
* **`nodes_of_retention_C11Q6`**：三者一起（K3 ∧ hnode ∧ hure）。
* **`nonempty_pre841Data_of_retention_C11Q6`**：端到端 ⇒ `Pre841Data_C11K`；相对 nodesScaled 端到端，
  `hnode hure hδ hact hfine hacc` 全部消去（`hacc` 由 `largerBallAccuracySupply_diagonal_C11S`），只剩
  块数据 `hev`、块支配 `hdom*`、`nr ≤ 1` 与 PRE841 种子数据。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 块 node 请求与 level 单调 -/

/-- 块 `m` 的 event node 请求：`kappaEventRequest_C11Q4` 在块输入处的值。 -/
def eventBlockRequest_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Λrec : ℝ)
    (Cderiv : ℝ≥0) (m : ℕ) (rad : ℝ) : ℝ × ℝ × ℕ × ℝ :=
  kappaEventRequest_C11Q4 P₀ g₀ Λrec Cderiv
    ((eventLevelE_C11Q4 (12 * (3 : ℝ) ^ m) + 1) * Real.sqrt ((3 : ℝ) ^ m))
    (Real.sqrt ((3 : ℝ) ^ m)) (rad / 100) ((rad ^ 2)⁻¹) 1

/-- 块 `m` 的 URE node 请求：`ureRequest_C11Q3` 在块输入处的值。 -/
def ureBlockRequest_C11Q6 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Λrec : ℝ)
    (Cderiv : ℝ≥0) (m : ℕ) (rad : ℝ) : ℝ × ℝ × ℕ × ℝ :=
  ureRequest_C11Q3 P₀ g₀ Λrec Cderiv
    (ureBlockD_C11Q3 (12 * (3 : ℝ) ^ m) * Real.sqrt ((3 : ℝ) ^ m))
    (Real.sqrt ((3 : ℝ) ^ m)) (rad / 100) ((rad ^ 2)⁻¹) 1

/-- event 低次水平集常数 `E_A` 在 `A ≥ 0` 上单调。 -/
theorem eventLevelE_mono_C11Q6 {A A' : ℝ} (hA : 0 ≤ A) (h : A ≤ A') :
    eventLevelE_C11Q4 A ≤ eventLevelE_C11Q4 A' := by
  unfold eventLevelE_C11Q4
  exact Real.exp_le_exp.mpr (by linarith [cutoffBarrierConst_mono_C11Q6 hA h])

/-- URE 作用量常数 `D(A) = factor(max A 1) + e^{9/2} + 4` 单调。 -/
theorem ureBlockD_mono_C11Q6 {A A' : ℝ} (h : A ≤ A') :
    ureBlockD_C11Q3 A ≤ ureBlockD_C11Q3 A' := by
  have hC := cutoffBarrierConst_mono_C11Q6 (A := max A 1) (A' := max A' 1)
    (le_max_of_le_right zero_le_one) (max_le_max h le_rfl)
  have hexp := Real.exp_le_exp.mpr (by linarith :
    cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2 ≤
      cutoffBarrierConst_C11Q3 (max A' 1) / 2 + 32 / Real.sqrt 2)
  change Real.exp (cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2) + 1 +
      Real.exp (9 / 2) + 4 ≤
    Real.exp (cutoffBarrierConst_C11Q3 (max A' 1) / 2 + 32 / Real.sqrt 2) + 1 +
      Real.exp (9 / 2) + 4
  linarith

theorem ureBlockD_pos_C11Q6 (A : ℝ) : 0 < ureBlockD_C11Q3 A := by
  change 0 < Real.exp (cutoffBarrierConst_C11Q3 (max A 1) / 2 + 32 / Real.sqrt 2) + 1 +
      Real.exp (9 / 2) + 4
  positivity

/-! ## 2. event node 数据（种子尺度版） -/

/-- **event node 数据 ⇐ 块数据**（`nonempty_pre841Data_of_native_nodesScaled_C11Q4` 的 `hnode` 逐字形，
`Cderiv = N.Ctime`、`δ = q.delta`、`α = diagonalAccuracy_C11S q.delta`）。 -/
theorem eventNodeData_of_blocks_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        N.params.neckRadius t / 100 ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho := by
  intro A hA n R H t p r hr hguard hsmall _ hscale x _ ϱ₀ hϱ₀ hball _
  have hev' := hev n
  choose blk hblk using hev'
  refine ⟨fun i => (eventLevelE_C11Q4 (12 * (3 : ℝ) ^ blk i) + 1) * Real.sqrt ((3 : ℝ) ^ blk i),
    fun i => Real.sqrt ((3 : ℝ) ^ blk i), fun i => rad (blk i + 1) / 100,
    fun i => (rad (blk i + 1) ^ 2)⁻¹, fun _ => 1, ?_⟩
  intro i hil hit
  beta_reduce
  have hr0 : 0 < r := hsmall.1
  have hst : H.time i.succ ≤ t :=
    (H.time_strictMono.monotone hil).trans (H.activeStage_time_le t)
  have hs2 : (t : ℝ) ≤ 2 * H.time i.succ := by nlinarith [sq_nonneg r]
  have hs3 : 3 * r ^ 2 / 2 < H.time i.succ := by nlinarith [sq_nonneg r]
  obtain ⟨-, hhi, hδ, hnr, hAg, hraw⟩ := hblk i
  have hAm : A < 12 * (3 : ℝ) ^ blk i := hAg A hA (hguard _ ⟨by linarith, hst⟩)
  have hradt : rad (blk i + 1) ≤ N.params.neckRadius t := hnr t ⟨hst, hs2⟩
  have hri := hrad (blk i + 1)
  have hd := hdomE (blk i)
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ blk i := one_le_pow₀ (by norm_num)
  refine ⟨Real.sqrt_nonneg _, div_pos hri (by norm_num), inv_pos.mpr (pow_pos hri 2), one_pos,
    ?_, by linarith, ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball
      (div_pos hri (by norm_num)) (by linarith), hδ.trans hd.2.2.2,
    hnr1 _ (H.time_nonneg _), ?_, ?_, ?_, ?_⟩
  · refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg r]
  · intro j hij _ b
    refine ((N.records n j).delta_le b).trans ?_
    have hlt : H.time i.succ ≤ H.time j.succ :=
      H.time_strictMono.monotone (hij.trans j.castSucc_le_succ)
    have hanti : N.params.delta (H.time j.succ) ≤ N.params.delta (H.time i.succ) :=
      N.delta_antitone (show H.time i.succ ∈ Ici (0 : ℝ) from H.time_nonneg _)
        (show H.time j.succ ∈ Ici (0 : ℝ) from H.time_nonneg _) hlt
    exact hanti.trans (hδ.trans hd.2.2.2)
  · intro j _ _ y s hs hst' hq
    have hs0 : 0 ≤ s := (H.time_nonneg j).trans hs.1.le
    refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hq)
    have hle : N.params.neckRadius t ≤ N.params.neckRadius s :=
      N.radius_antitone (show s ∈ Ici (0 : ℝ) from hs0)
        (show (t : ℝ) ∈ Ici (0 : ℝ) from t.2.1) hst'
    exact inv_anti₀ (pow_pos hri 2) (pow_le_pow_left₀ hri.le (hradt.trans hle) 2)
  · exact uniformCaps_of_raw_C11Q6 ((N.records n i).static)
      (fun c => (hraw c).imp fun _ h => ⟨h.1, h.2.1⟩) _ hd.1 hd.2.1 hd.2.2.1
  · have hmax : max A 1 ≤ 12 * (3 : ℝ) ^ blk i := max_le hAm.le (by linarith)
    have hE := eventLevelE_mono_C11Q6 (le_max_of_le_right zero_le_one) hmax
    have hr3 : r ≤ Real.sqrt ((3 : ℝ) ^ blk i) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
    have hE0 : 0 ≤ eventLevelE_C11Q4 (12 * (3 : ℝ) ^ blk i) + 1 := by
      unfold eventLevelE_C11Q4
      positivity
    exact mul_le_mul (by linarith) hr3 hr0.le hE0

/-! ## 3. URE node 数据 -/

/-- URE 窗口 event 的时刻：`activeStage a ≤ i.castSucc` ⇒ `a < time i.succ`。 -/
theorem lt_time_succ_of_activeStage_le_C11Q6 (H : ObservedHistory.{u})
    (a : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc) :
    (a : ℝ) < H.time i.succ := by
  have hv := Fin.le_iff_val_le_val.mp hf
  simp only [Fin.val_castSucc] at hv
  have hk : (H.activeStage a).val < H.eventCount := by omega
  have h1 := H.activeStage_before_next a hk
  have h2 : H.time ⟨(H.activeStage a).val + 1, by omega⟩ ≤ H.time i.succ := by
    apply H.time_strictMono.monotone
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_succ]
    omega
  exact lt_of_lt_of_le h1 h2

/-- **URE node 数据 ⇐ 块数据**（`hure` 逐字形）。 -/
theorem ureNodeData_of_blocks_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho := by
  intro A hA n R H t p r hr hguard hsmall _ x _ ϱ₀ hϱ₀ hball a ha
  have hev' := hev n
  choose blk hblk using hev'
  have hr0 : 0 < r := hsmall.1
  have hw2 : (Real.sqrt 3 * r / 2) ^ 2 = 3 / 4 * r ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hfacts : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc →
      i.succ ≤ H.activeStage t →
      H.time i.succ ≤ t ∧ (t : ℝ) ≤ 2 * H.time i.succ ∧ 5 * r ^ 2 / 4 < H.time i.succ := by
    intro i hf hl
    have hst : H.time i.succ ≤ t :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
    have hai := lt_time_succ_of_activeStage_le_C11Q6 H a i hf
    rw [ha, hw2] at hai
    exact ⟨hst, by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r]⟩
  refine ⟨fun i => ureBlockD_C11Q3 (12 * (3 : ℝ) ^ blk i) * Real.sqrt ((3 : ℝ) ^ blk i),
    fun i => Real.sqrt ((3 : ℝ) ^ blk i), fun i => rad (blk i + 1) / 100,
    fun i => (rad (blk i + 1) ^ 2)⁻¹, fun _ => 1, ?_, ?_⟩
  · intro i hf hl
    beta_reduce
    obtain ⟨hst, hs2, hs5⟩ := hfacts i hf hl
    obtain ⟨-, hhi, hδ, hnr, -, hraw⟩ := hblk i
    have hradt : rad (blk i + 1) ≤ N.params.neckRadius t := hnr t ⟨hst, hs2⟩
    have hri := hrad (blk i + 1)
    have hd := hdomU (blk i)
    refine ⟨Real.sqrt_nonneg _, div_pos hri (by norm_num), inv_pos.mpr (pow_pos hri 2), one_pos,
      ?_, ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball
        (div_pos hri (by norm_num)) (by linarith), hδ.trans hd.2.2.2,
      hnr1 _ (H.time_nonneg _), ?_, ?_, ?_⟩
    · refine Real.le_sqrt_of_sq_le ?_
      rw [hw2]
      nlinarith [sq_nonneg r]
    · intro j hij _ b
      refine ((N.records n j).delta_le b).trans ?_
      have hlt : H.time i.succ ≤ H.time j.succ :=
        H.time_strictMono.monotone (hij.trans j.castSucc_le_succ)
      have hanti : N.params.delta (H.time j.succ) ≤ N.params.delta (H.time i.succ) :=
        N.delta_antitone (show H.time i.succ ∈ Ici (0 : ℝ) from H.time_nonneg _)
          (show H.time j.succ ∈ Ici (0 : ℝ) from H.time_nonneg _) hlt
      exact hanti.trans (hδ.trans hd.2.2.2)
    · intro j _ _ y s hs hst' hq
      have hs0 : 0 ≤ s := (H.time_nonneg j).trans hs.1.le
      refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hq)
      have hle : N.params.neckRadius t ≤ N.params.neckRadius s :=
        N.radius_antitone (show s ∈ Ici (0 : ℝ) from hs0)
          (show (t : ℝ) ∈ Ici (0 : ℝ) from t.2.1) hst'
      exact inv_anti₀ (pow_pos hri 2) (pow_le_pow_left₀ hri.le (hradt.trans hle) 2)
    · exact blockCaps_of_raw_C11Q6 ((N.records n i).static)
        (fun c => (hraw c).imp fun _ h => ⟨h.1, h.2.1⟩) _ hd.1 hd.2.1 hd.2.2.1
  · intro i hf hl
    beta_reduce
    obtain ⟨hst, hs2, hs5⟩ := hfacts i hf hl
    obtain ⟨-, hhi, -, -, hAg, -⟩ := hblk i
    have hs2' : (t : ℝ) / 2 ≤ H.time i.succ := by linarith
    have hAm : A < 12 * (3 : ℝ) ^ blk i := hAg A hA (hguard _ ⟨hs2', hst⟩)
    have hr3 : r ≤ Real.sqrt ((3 : ℝ) ^ blk i) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
    exact mul_le_mul (ureBlockD_mono_C11Q6 hAm.le) hr3 hr0.le (ureBlockD_pos_C11Q6 _).le

/-! ## 4. 三者一起与端到端 -/

/-- **R1 打包（K3 ∧ event node ∧ URE node）**：块数据 `hev` + 三类块支配 ⇒ κ 线的三份 cap 供给。 -/
theorem nodes_of_retention_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hdomK3 : ∀ m : ℕ,
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
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    (SurgeryActionBarrier_C11Q F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1)))) ∧
    (∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        N.params.neckRadius t / 100 ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho) ∧
    (∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        ∀ a : Icc (0 : ℝ) H.horizon, (a : ℝ) = (t : ℝ) - (Real.sqrt 3 * r / 2) ^ 2 →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          UREBlockNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r A a
            nodeA nodeE nodeR nodeQ nodeRho) :=
  ⟨surgeryActionBarrier_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3,
    eventNodeData_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomE,
    ureNodeData_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomU⟩

/-- **端到端（R1）⇒ `Pre841Data_C11K`**：KAPPA3 nodesScaled 端到端的证明链（K3 → K4 scaled → K5 → P6B →
late window → PRE841），K3 / hnode / hure 由 `nodes_of_retention_C11Q6`，`hacc` 由
`largerBallAccuracySupply_diagonal_C11S`；**无** `hact`、`hfine`。 -/
theorem nonempty_pre841Data_of_retention_C11Q6 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hdomK3 : ∀ m : ℕ,
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
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨hK3, hnode, hure⟩ :=
    nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hK4 := boundedReducedLengthScaled_of_end_C11Q4
    (weightedMinBoundEndScaled_of_nodeData_C11Q4 N.params N.records N.Ctime hnode) hK3
    (fun _ _ => le_rfl)
  have hK5 := seedReducedVolumeScaled_of_block_C11Q4 (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)
  have hloc : LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 hK5
  obtain ⟨κ₁, hκ₁, hW₁⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B
      (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW₁ hsmallScale
  exact ⟨pre841Data_of_window_C11K (lt_min hκ₁ hκ') hW0 ind (N.comp ind) t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist⟩

/-- **consumer（型对齐，lead 要求）**：本文件的 `hnode / hure` 直接喂 KAPPA3 G6 的
`nonempty_pre841Data_of_native_nodesScaled_C11Q4`（`hact / hfine` 照旧作为它自己的前提）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
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
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params (diagonalAccuracy_C11S N.params.delta)
      (weightedMinLevel_C11Q2 (fun A => cutoffBarrierConst_C11Q3 (max A 1))) N.Ctime)
    {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  exact nonempty_pre841Data_of_native_nodesScaled_C11Q4 N N.Ctime
    (eventNodeData_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomE)
    (ureNodeData_of_blocks_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomU) (fun _ _ => le_rfl)
    hact hfine (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hA hκ'
    hsmallScale ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii
    hwin hdist

end GC.LongTime.Ch11
