import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineScaleC11Q5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q2

/-!
# fine-cap 端到端：block 常数、"∀ t 可满足"、native ⇒ Pre841（O-CH11-FINECAP G2，后缀 `_C11Q5`）

**D-2 contract correction**（`docs/geometrization/chapter8/design-C11-finecap-20261007.md` §0′）：
`nonempty_pre841Data_of_native_C11Q2` 的 `hscale : KappaWindowScale_C11Q2 P g N.params …` **推不出**——
`windowBarrierConsts_C11Q2` 是 `Classical.choose`（无单调 / 衰减导出），`WindowBarrierSpec_C11Q2` 对 `ε₀`
向下封闭、对 `R₀, m₀` 向上封闭，而 `N.params.modelAccuracy > 0`（`modelAccuracy_pos`）、`modelRadius`、
`modelOrder` 是固定数，故 `∀ A ∀ t, modelAccuracy ≤ ε₀(A,t)` 不可由任何不提 chooser 内部值的前提导出。
(b′) **替换**它：`hscale` ⟶ `hact`（每个 static cap 的实际 canonical 插入证书）+ `hfine`
（`KappaFineScale_C11Q5`：只约束 `α` 的纯 δ 条件，无 model tuple 子句）。

* **block 常数**：`k(t) = Int.clog 2 t`（`2^{k−1} < t ≤ 2^k`），请求输入取 block 最坏情形
  `E = √(2^k/2)`、`A_act = Λ_A·E`、`r₀ = nr(2^k)/100`、`qcan = nr(2^k)^{−2}`、`ρ = nr(2^k/4)`（由
  `radius_antitone` 覆盖 `t` 的实际需要），故 δ 预算只依赖 `(A, k(t))`：`fineCapDeltaBlock_C11Q5`。
* `KappaFineScale_C11Q5`（接口 (4) 的 native 形）：`∀ A > 0, ∀ t > 0, ∀ s ∈ [t/2, t], α A s ≤
  fineCapDeltaBlock(A, k(t))`。
* **"∀ t 可满足"** `kappaFineScale_of_envelope_C11Q5`：逐点正包络 `fineCapEnvelope_C11Q5 A s =
  min(δ_blk(A, k(s)), δ_blk(A, k(s)+1)) > 0`（`fineCapEnvelope_pos_C11Q5`）；`α A s ≤ 包络` ⇒
  `KappaFineScale`（`s ∈ [t/2, t] ⇒ k(t) ∈ {k(s), k(s)+1}`）。剩余只是 S7 侧 `δ < α ≤ 包络`。
* native K3 `surgeryActionBarrier_of_native_fineCap_C11Q5`、
  `localKappaWideSupply_of_native_fineCap_C11Q5`、
  端到端 `nonempty_pre841Data_of_native_fineCap_C11Q5`（binder 与 `_C11Q2` 逐字相同，只换 `hscale`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 二进 block -/

/-- block 指标 `k(t) = ⌈log₂ t⌉`（`Int.clog 2 t`）。 -/
def blockIndex_C11Q5 (t : ℝ) : ℤ := Int.clog 2 t

/-- block 上端 `2^k`。 -/
def blockTime_C11Q5 (k : ℤ) : ℝ := (2 : ℝ) ^ k

theorem blockTime_pos_C11Q5 (k : ℤ) : 0 < blockTime_C11Q5 k := zpow_pos (by norm_num) k

theorem le_blockTime_C11Q5 (t : ℝ) : t ≤ blockTime_C11Q5 (blockIndex_C11Q5 t) := by
  have h := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) t
  unfold blockTime_C11Q5 blockIndex_C11Q5
  exact_mod_cast h

theorem blockTime_lt_C11Q5 {t : ℝ} (ht : 0 < t) : blockTime_C11Q5 (blockIndex_C11Q5 t) < 2 * t := by
  have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) ht
  simp only [Nat.cast_ofNat] at h
  unfold blockTime_C11Q5 blockIndex_C11Q5
  rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
  linarith

theorem blockIndex_le_C11Q5 {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    blockIndex_C11Q5 s ≤ blockIndex_C11Q5 t :=
  Int.clog_mono_right hs hst

theorem blockIndex_le_succ_C11Q5 {s t : ℝ} (ht : 0 < t) (hts : t ≤ 2 * s) :
    blockIndex_C11Q5 t ≤ blockIndex_C11Q5 s + 1 := by
  refine (Int.le_zpow_iff_clog_le (R := ℝ) (b := 2) (by norm_num) ht).mp ?_
  have h := le_blockTime_C11Q5 s
  unfold blockTime_C11Q5 at h
  simp only [Nat.cast_ofNat]
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-! ## 2. block 请求与 δ 预算 -/

/-- block `k` 的 δ 预算：`fineCapDelta_C11Q5` 在 block 最坏情形输入
`(√(2^k/2), nr(2^k)/100, nr(2^k)^{−2}, nr(2^k/4))` 处的值。 -/
def fineCapDeltaBlock_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (ΛA : ℝ) (Ctime : ℝ≥0) (k : ℤ) : ℝ :=
  fineCapDelta_C11Q5 P₀ g₀ params.fixed ΛA params.recenterConstant
    (fun _ => Real.sqrt (blockTime_C11Q5 k / 2))
    (fun _ => params.neckRadius (blockTime_C11Q5 k) / 100)
    (fun _ => (params.neckRadius (blockTime_C11Q5 k) ^ 2)⁻¹)
    (fun _ => params.neckRadius (blockTime_C11Q5 k / 4)) Ctime 0

theorem fineCapDeltaBlock_pos_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (ΛA : ℝ) (Ctime : ℝ≥0) (k : ℤ) :
    0 < fineCapDeltaBlock_C11Q5 P₀ g₀ params ΛA Ctime k := by
  have hT := blockTime_pos_C11Q5 k
  have hρ := params.neckRadius_pos (blockTime_C11Q5 k) hT.le
  exact fineCapDelta_pos_C11Q5 P₀ g₀ params.fixed ΛA _ _ _ _ Ctime (Real.sqrt_nonneg _)
    (by positivity) (inv_pos.mpr (pow_pos hρ 2))
    (lt_of_lt_of_le (by norm_num) params.recenterConstant_ge_four)
    (params.neckRadius_pos _ (by positivity))

/-- **接口 (4) 的 native 形**（代替 `KappaWindowScale_C11Q2`）：纯 δ 条件，无 model tuple 子句。 -/
def KappaFineScale_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (α : ℝ → ℝ → ℝ) (Λ : ℝ → ℝ) (Ctime : ℝ≥0) : Prop :=
  ∀ A, 0 < A → ∀ t : ℝ, 0 < t → ∀ s ∈ Icc (t / 2) t,
    α A s ≤ fineCapDeltaBlock_C11Q5 P₀ g₀ params (Λ A) Ctime (blockIndex_C11Q5 t)

/-- **逐点正包络** `δ̄(A, s) = min(δ_blk(A, k(s)), δ_blk(A, k(s)+1))`。 -/
def fineCapEnvelope_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Λ : ℝ → ℝ) (Ctime : ℝ≥0) (A s : ℝ) : ℝ :=
  min (fineCapDeltaBlock_C11Q5 P₀ g₀ params (Λ A) Ctime (blockIndex_C11Q5 s))
    (fineCapDeltaBlock_C11Q5 P₀ g₀ params (Λ A) Ctime (blockIndex_C11Q5 s + 1))

theorem fineCapEnvelope_pos_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) (Λ : ℝ → ℝ) (Ctime : ℝ≥0) (A s : ℝ) :
    0 < fineCapEnvelope_C11Q5 P₀ g₀ params Λ Ctime A s :=
  lt_min (fineCapDeltaBlock_pos_C11Q5 P₀ g₀ params _ Ctime _)
    (fineCapDeltaBlock_pos_C11Q5 P₀ g₀ params _ Ctime _)

/-- **"对所有 t 可满足"**：`α` 被逐点正包络控制 ⇒ `KappaFineScale_C11Q5`。 -/
theorem kappaFineScale_of_envelope_C11Q5 (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (params : CutoffParameters) {α : ℝ → ℝ → ℝ} (Λ : ℝ → ℝ) (Ctime : ℝ≥0)
    (hα : ∀ A, 0 < A → ∀ s, 0 < s → α A s ≤ fineCapEnvelope_C11Q5 P₀ g₀ params Λ Ctime A s) :
    KappaFineScale_C11Q5 P₀ g₀ params α Λ Ctime := by
  intro A hA t ht s hs
  have hs0 : 0 < s := lt_of_lt_of_le (half_pos ht) hs.1
  have h1 := blockIndex_le_C11Q5 hs0 hs.2
  have h2 := blockIndex_le_succ_C11Q5 ht (by linarith [hs.1] : t ≤ 2 * s)
  refine (hα A hA s hs0).trans ?_
  rcases (show blockIndex_C11Q5 t = blockIndex_C11Q5 s ∨
      blockIndex_C11Q5 t = blockIndex_C11Q5 s + 1 by omega) with h | h
  · rw [h]
    exact min_le_left _ _
  · rw [h]
    exact min_le_right _ _

/-! ## 3. native ⇒ K3 -/

/-- **K3 由 native 数据 + fine-cap**：block 输入（`Eb, r₀, qcan, ρbar` 只依赖 `k(t)`）+ `hact` + `hfine`
⇒ `SurgeryActionBarrier_C11Q`（对照 `surgeryActionBarrier_of_native_C11Q2` 的 `hscale`）。 -/
theorem surgeryActionBarrier_of_native_fineCap_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {Λ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s) (hΛ : ∀ A, 0 < A → 0 < Λ A)
    (hfine : KappaFineScale_C11Q5 P g N.params α Λ N.Ctime) :
    SurgeryActionBarrier_C11Q F δ α N.params.neckRadius Λ := by
  have hanti := N.radius_antitone
  refine surgeryActionBarrier_of_fineCap_C11Q5 N.params N.records hact hδ hΛ
    (fun t => Real.sqrt (blockTime_C11Q5 (blockIndex_C11Q5 t) / 2))
    (fun t => N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 t)) / 100)
    (fun t => (N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 t)) ^ 2)⁻¹)
    (fun t => N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 t) / 4))
    ?_ ?_ ?_ ?_ ?_ N.Ctime ?_ hfine
  · intro t _
    exact Real.sqrt_le_sqrt (by linarith [le_blockTime_C11Q5 t])
  · intro t ht
    have hT := blockTime_pos_C11Q5 (blockIndex_C11Q5 t)
    refine ⟨by have := N.params.neckRadius_pos _ hT.le; positivity, ?_⟩
    have hmono := hanti (show t ∈ Ici (0 : ℝ) from ht.le)
      (show blockTime_C11Q5 (blockIndex_C11Q5 t) ∈ Ici (0 : ℝ) from hT.le) (le_blockTime_C11Q5 t)
    linarith
  · intro t _
    have hT := blockTime_pos_C11Q5 (blockIndex_C11Q5 t)
    exact inv_pos.mpr (pow_pos (N.params.neckRadius_pos _ hT.le) 2)
  · intro t _
    have hT := blockTime_pos_C11Q5 (blockIndex_C11Q5 t)
    exact N.params.neckRadius_pos _ (by positivity)
  · intro t s ht hs1 _
    have hT := blockTime_pos_C11Q5 (blockIndex_C11Q5 t)
    have hlt := blockTime_lt_C11Q5 ht
    exact hanti (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  · intro n t j y _ s hs hst hq
    refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hq)
    have hs0 : 0 ≤ s := ((F.tower.history n).toHistory.time_nonneg j).trans hs.1.le
    have hT := blockTime_pos_C11Q5 (blockIndex_C11Q5 (t : ℝ))
    have hρs := N.params.neckRadius_pos s hs0
    have hρT := N.params.neckRadius_pos _ hT.le
    have hle : N.params.neckRadius (blockTime_C11Q5 (blockIndex_C11Q5 (t : ℝ))) ≤
        N.params.neckRadius s :=
      hanti (show s ∈ Ici (0 : ℝ) from hs0)
        (show blockTime_C11Q5 (blockIndex_C11Q5 (t : ℝ)) ∈ Ici (0 : ℝ) from hT.le)
        (hst.le.trans (le_blockTime_C11Q5 t))
    exact inv_anti₀ (pow_pos hρT 2) (pow_le_pow_left₀ hρT.le hle 2)

/-- **局部 κ（尺度 ≥ neckRadius/100）由 native 数据 + fine-cap**：`localKappaWideSupply_of_native_C11Q2`
的 `hscale` 换成 `hact` + `hfine`。 -/
theorem localKappaWideSupply_of_native_fineCap_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime) :
    LocalKappaWideSupply_C11Q F δ α N.params.neckRadius :=
  localKappa_of_weightedMinBound_block_C11Q2 hW
    (surgeryActionBarrier_of_native_fineCap_C11Q5 N hact hδ
      (fun A _ => weightedMinLevel_pos_C11Q2 C A) hfine)
    (fun _ _ => le_rfl) hB hκ

/-! ## 4. 端到端 -/

/-- **端到端 ⇒ `Pre841Data_C11K`（fine-cap 版）**：binder 与 `nonempty_pre841Data_of_native_C11Q2`
逐字相同，只把 `hscale : KappaWindowScale_C11Q2 …` 换成 `hact` + `hfine`（D-2 contract correction：
`hscale` 推不出，见文件头）。证明与 `_C11Q2` 相同（S7 + Q3 ⇒ `nr := 0` window ⇒ PRE841）。 -/
theorem nonempty_pre841Data_of_native_fineCap_C11Q5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
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
  have hloc : LocalKappaSupply_P6B F δ α N.params.neckRadius :=
    (localKappaWideSupply_of_native_fineCap_C11Q5 N hW hB hκ hδ hact hfine).toP6B
  obtain ⟨κ₁, hκ₁, hW₁⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW₁ hsmallScale
  exact ⟨pre841Data_of_window_C11K (lt_min hκ₁ hκ') hW0 ind (N.comp ind) t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist⟩

/-- **binder 逐字对齐（lead 条件 (1)）**：binder 取自 `nonempty_pre841Data_of_native_C11Q2`（逐字，只把
`hscale` 换成 `hact` + `hfine`），位置参数顺序与 `_C11Q2` 相同。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hact : ∀ n i b, ActualCanonicalInsertion_C11Q5 ((N.records n i).static b))
    (hfine : KappaFineScale_C11Q5 P g N.params α (weightedMinLevel_C11Q2 C) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
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
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) :=
  nonempty_pre841Data_of_native_fineCap_C11Q5 N hW hB hκ hδ hact hfine hacc hA hκ' hsmallScale ind t
    p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist

end GC.LongTime.Ch11
