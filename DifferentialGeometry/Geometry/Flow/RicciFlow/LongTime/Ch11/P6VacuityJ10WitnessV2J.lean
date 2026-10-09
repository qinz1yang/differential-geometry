import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12V11mHcolCHN_HPC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ParamCompatTwoP6SS

set_option autoImplicit false

/-!
# VAC2-J10 审计见证（`_V2J`）：J10ResE_DJ 窗口形、hsepX 缺口与充分性、HNF 抬高、HPC 槽、εP6

* **(A) J10 帧窗口形（PROVED）**：`extendAt` = `extendHorizon`（eventCount 不变，horizon = `t`）；
  `J10ResE_DJ` 的 `hsT : ts ≤ Tn` 与 `Tn ≤ horizon = ts` 强迫 `Tn = ts`（`eq_extendAtTime_of_le_V2J`），
  故 `aSeed = σ − r²`，`r` 为 ∃ 常数（与 n 无关）：hsepX 是**固定单位窗**（非 T/R 窗）。
* **(B) hsepX 缺口非空（GAP-WITNESS，抽象序列）**：DrvResE 输出的 T/R 窗形不蕴含固定窗形
  （`hsepX_gap_witness_V2J`）——HSEPX 须真输入，非机械。
* **(C) hsepX 充分性（PROVED，数值核）**：record `r < δ²ρ(e)`（nominal_small）+ hpc
  `δ(e)ρ(e) ≤ ρ(Tn)`（`Tn ≤ 2e`，`window_half_V2J`）+ ceiling `R ≤ ρ(Tn)⁻²` ⇒ `R < δ²·scale`
  （`scale_ratio_V2J`）；配 `δ → 0`（BlockTower `cap_le_level`）⇒ `∀ M, ∀ᶠ n, M·R < scale`
  （`hsepX_of_ratio_V2J`）。故 hsepX **不可反驳**，但依赖 hpc ⇒ 只能建在 `_HPC` 槽（hpc 为前提）上。
* **(D) HNF 抬高（PROVED，泛型）**：J10ResE_DJ 中 `T₀` 的全部出现均为门控（records / δb / scale /
  a₀·scale / hcanWin / hnot）或 `Ici T₀` 截集或 `∀ B, ∀ᶠ` 上界；前两类对 `T₀` 反单调
  （`gate_mono_V2J`、`slabSet_mono_V2J`、`phiAlmost_mono_V2J`），第三类尾相等即保持 ⇒ 抬高不引入错配。
* **(E) R52 机器核（PROVED）**：`_HPC` 孪生槽体（`SurgeryParamCompat_P6PC q 2 → K`）在 bad tower 上
  **可居**（`hpcSlotE6_of_badTower_V2J` / `hpcSlotJ8_of_badTower_V2J`），而旧槽体在同一 tower 上为假
  （`oldSlotE6_false_of_badTower_V2J`）：VAC badTower 模板不再推出 `False`。
* **(F) εP6 选择子（PROVED）**：新 `_hTRs` 的 modelAccuracy 上界为正且 ≤ `εSel_W9S`
  （`hTRs_accBound_pos_V2J`、`exists_acc_V2J`），与 hres 槽的 `≤ εSel_W9S` 相容（非 F241 型）。
-/

noncomputable section
universe u
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CHN p6X2HN_CHN p6CtimeHN_CHN p6BadCHN_CHN htransMBadHN_CHN)

/-! ## (A) J10 帧窗口形 -/

namespace RetainedCoreHistory

/-- `extendAt` 的 horizon 即 `t`（`_V2J`，定义等）。 -/
theorem extendAt_horizon_V2J (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) :
    (H.extendAt hend G hG hat hts).toHistory.horizon = t := rfl

/-- `extendAt` 不新增事件（`_V2J`）。 -/
theorem extendAt_eventCount_V2J (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) :
    (H.extendAt hend G hG hat hts).eventCount = H.eventCount := rfl

/-- **窗口形（`_V2J`）**：J10 帧 `ts ≤ Tn` ⇒ `Tn = ts`（`ts` 即 horizon）。 -/
theorem eq_extendAtTime_of_le_V2J (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (Tn : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon)
    (h : H.extendAtTime hend G hG hat hts ≤ Tn) : Tn = H.extendAtTime hend G hG hat hts :=
  Subtype.ext (le_antisymm Tn.2.2 h)

/-- **aSeed 形（`_V2J`）**：`aSeed = Tn − r²` 且 `ts ≤ Tn` ⇒ `aSeed = t − r²`（`r` 与 n 无关）。 -/
theorem aSeed_eq_V2J (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (Tn aSeed : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon) (r : ℝ)
    (h : H.extendAtTime hend G hG hat hts ≤ Tn) (ha : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2) :
    (aSeed : ℝ) = t - r ^ 2 := by
  rw [ha, H.eq_extendAtTime_of_le_V2J hend G hG hat hts Tn h]
  rfl

end RetainedCoreHistory

/-! ## (B) hsepX 缺口：T/R 窗形不蕴含固定窗形 -/

/-- 抽象曲率 `R n = (n+1)²`。 -/
def gapR_V2J : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2

/-- 抽象事件年龄 `1/(n+1)`（→ 0，但 ≫ T/R）。 -/
def gapAge_V2J : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)

/-- 抽象 neck scale `2R`。 -/
def gapScale_V2J : ℕ → ℝ := fun n => 2 * gapR_V2J n

/-- DrvResE 输出形（T/R 窗）在抽象序列上成立（窗内终于无事件）。 -/
theorem gap_tR_window_V2J : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
    gapAge_V2J n < T / gapR_V2J n →
      2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * gapR_V2J n) < gapScale_V2J n := by
  intro T _ C _
  filter_upwards [eventually_gt_atTop ⌈T⌉₊] with n hn h
  exfalso
  have hT : T < (n : ℝ) + 1 := by
    have h1 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    have h2 : (⌈T⌉₊ : ℝ) < n := by exact_mod_cast hn
    linarith
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold gapAge_V2J gapR_V2J at h
  rw [div_lt_div_iff₀ hp (by positivity)] at h
  nlinarith

/-- 固定窗形（hsepX）在同一抽象序列上对任意 `r > 0` 失败（`M = 2`）。 -/
theorem gap_not_fixed_window_V2J : ∀ r : ℝ, 0 < r → ¬ ∀ M : ℝ, ∀ᶠ n in atTop,
    gapAge_V2J n < r ^ 2 → M * gapR_V2J n < gapScale_V2J n := by
  intro r hr h
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (pow_pos hr 2)
  obtain ⟨n, hn, hle⟩ := ((h 2).and (eventually_ge_atTop N)).exists
  have hp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hle
  have hage : gapAge_V2J n < r ^ 2 :=
    lt_of_le_of_lt (one_div_le_one_div_of_le hp hNn) hN
  have := hn hage
  unfold gapScale_V2J at this
  exact lt_irrefl _ this

/-- **GAP-WITNESS（hsepX 窗口形）**：满足 kernel 假设 `n+1 ≤ R` 的抽象序列上，T/R 窗输出成立而
固定窗 hsepX 对任意 `r` 失败 ⇒ hsepX 不能由 DrvResE 输出机械推出。 -/
theorem hsepX_gap_witness_V2J :
    (∀ n : ℕ, (n : ℝ) + 1 ≤ gapR_V2J n) ∧
    (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      gapAge_V2J n < T / gapR_V2J n →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * gapR_V2J n) < gapScale_V2J n) ∧
    (∀ r : ℝ, 0 < r → ¬ ∀ M : ℝ, ∀ᶠ n in atTop,
      gapAge_V2J n < r ^ 2 → M * gapR_V2J n < gapScale_V2J n) := by
  refine ⟨fun n => ?_, gap_tR_window_V2J, gap_not_fixed_window_V2J⟩
  unfold gapR_V2J
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-! ## (C) hsepX 充分性 -/

/-- **数值核（`_V2J`）**：`r < δ²ρe`、`δρe ≤ ρT`、`R ≤ ρT⁻²` ⇒ `R < δ²·r⁻²`。 -/
theorem scale_ratio_V2J {δ ρe ρT r R : ℝ} (hδ : 0 < δ) (hρe : 0 < ρe) (hr : 0 < r)
    (hnom : r < δ ^ 2 * ρe) (hpc : δ * ρe ≤ ρT) (hceil : R ≤ (ρT ^ 2)⁻¹) :
    R < δ ^ 2 * (r ^ 2)⁻¹ := by
  have hdp : 0 < δ * ρe := mul_pos hδ hρe
  have h1 : (ρT ^ 2)⁻¹ ≤ ((δ * ρe) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hdp 2) (pow_le_pow_left₀ hdp.le hpc 2)
  have h2 : ((δ ^ 2 * ρe) ^ 2)⁻¹ < (r ^ 2)⁻¹ :=
    inv_strictAnti₀ (pow_pos hr 2) (pow_lt_pow_left₀ hnom hr.le two_ne_zero)
  have h3 : ((δ * ρe) ^ 2)⁻¹ = δ ^ 2 * ((δ ^ 2 * ρe) ^ 2)⁻¹ := by
    field_simp
  have h4 : δ ^ 2 * ((δ ^ 2 * ρe) ^ 2)⁻¹ < δ ^ 2 * (r ^ 2)⁻¹ :=
    mul_lt_mul_of_pos_left h2 (pow_pos hδ 2)
  linarith

/-- **hsepX ⇐ 比值 + δ→0（`_V2J`）**。 -/
theorem hsepX_of_ratio_V2J (R scale δ : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hrat : ∀ n, R n < δ n ^ 2 * scale n) :
    ∀ M : ℝ, ∀ᶠ n in atTop, M * R n < scale n := by
  intro M
  have hM : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hδ2 : Tendsto (fun n => δ n ^ 2) atTop (𝓝 0) := by
    simpa using hδ.pow 2
  filter_upwards [hδ2.eventually (gt_mem_nhds (one_div_pos.mpr hM))] with n hn
  have hRn := hR n
  have hrn := hrat n
  have hs : 0 < scale n := by
    by_contra hc
    replace hc := not_lt.mp hc
    nlinarith [sq_nonneg (δ n)]
  have hk : max M 1 * δ n ^ 2 < 1 := by
    rw [lt_div_iff₀ hM] at hn
    linarith
  calc M * R n ≤ max M 1 * R n := mul_le_mul_of_nonneg_right (le_max_left _ _) hRn.le
    _ < max M 1 * (δ n ^ 2 * scale n) := mul_lt_mul_of_pos_left hrn hM
    _ = (max M 1 * δ n ^ 2) * scale n := by ring
    _ < 1 * scale n := mul_lt_mul_of_pos_right hk hs
    _ = scale n := one_mul _

/-- **窗口 ⊂ [Tno/2, Tno]（`_V2J`）**：`2c < cTn`（即 `2r_k² < Tno`）、`Tn − 1/2 ≤ σ`、
`c(σ − r²) ≤ e`、`r² ≤ 1/2` ⇒ `cTn ≤ 2e`（hpc θ=2 适用）。 -/
theorem window_half_V2J {c Tn σ e r : ℝ} (hc : 0 < c) (h2 : 2 * c < c * Tn)
    (hσ : Tn - 1 / 2 ≤ σ) (he : c * (σ - r ^ 2) ≤ e) (hr : r ^ 2 ≤ 1 / 2) :
    c * Tn ≤ 2 * e := by
  nlinarith

/-- hpc（θ=2）在窗口上的用法（`_V2J`）：`δ(e)ρ(e) ≤ ρ(Tno)`。 -/
theorem compat_window_V2J (q : CutoffParameters) (hpc : SurgeryParamCompat_P6PC q 2)
    {e Tno : ℝ} (he0 : 0 ≤ e) (heT : e ≤ Tno) (hT2 : Tno ≤ 2 * e) :
    q.delta e * q.neckRadius e ≤ q.neckRadius Tno :=
  hpc.2 e Tno he0 heT hT2

/-! ## (D) HNF 抬高：门控反单调 -/

/-- 门控命题对阈值反单调（`_V2J`）。 -/
theorem gate_mono_V2J {ι : Type*} (τ : ι → ℝ) (P : ι → Prop) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ i, a ≤ τ i → P i) : ∀ i, b ≤ τ i → P i :=
  fun i hi => h i (hab.trans hi)

/-- `Ico ∩ Ici T₀` 截集对 `T₀` 反单调（`_V2J`）。 -/
theorem slabSet_mono_V2J {x y a b : ℝ} (hab : a ≤ b) : Ico x y ∩ Ici b ⊆ Ico x y ∩ Ici a :=
  fun _ ht => ⟨ht.1, le_trans hab ht.2⟩

/-- `PhiAlmostNonnegative` 对集合反单调（`_V2J`）：抬高 `T₀` 后 Φ 合取更弱。 -/
theorem phiAlmost_mono_V2J {K : RetainedCoreHistory.{u}} (j : Fin K.eventCount) {Phi : ℝ → ℝ}
    {W W' : Set ℝ}
    (hW : W' ⊆ W)
    (h : Perelman.PhiAlmostNonnegative (K.toHistory.event j).incoming.flow W Phi) :
    Perelman.PhiAlmostNonnegative (K.toHistory.event j).incoming.flow W' Phi :=
  fun t ht x => h t (hW ht) x

/-! ## (E) R52 机器核：HPC 孪生槽在 bad tower 上可居 -/

namespace ObservedHistory

/-- **HPC 槽体（E6，`_V2J`）在 bad tower 上平凡成立**（`Θ := 0`，hpc 前提与 `¬hpc` 矛盾）。 -/
theorem hpcSlotE6_of_badTower_V2J {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} {Cdist : ℝ≥0} {εR : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hbad : ¬ SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2)
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) (a₀ : ℝ) :
    ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      SurgeryParamCompat_P6PC q 2 →
      HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨fun _ => 0, fun _ _ _ _ _ _ hpc => absurd
    (paramCompat_of_eqOn_P6SS hpc fun t ht => ⟨(hq t ht).1.symm, (hq t ht).2.symm⟩) hbad⟩

/-- **HPC 槽体（J8，`_V2J`）在 bad tower 上平凡成立**。 -/
theorem hpcSlotJ8_of_badTower_V2J {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} {Cdist : ℝ≥0} {εR : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hbad : ¬ SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2)
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) (a₀ : ℝ) :
    ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      SurgeryParamCompat_P6PC q 2 →
      HgwResJ8H_V11_CHN F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨fun _ => 0, fun _ _ _ _ _ _ hpc => absurd
    (paramCompat_of_eqOn_P6SS hpc fun t ht => ⟨(hq t ht).1.symm, (hq t ht).2.symm⟩) hbad⟩

/-- **对照（旧槽体，`_V2J`）**：无 hpc 前提的槽体在同一 bad tower 上为假（VAC 模板）。 -/
theorem oldSlotE6_false_of_badTower_V2J {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants} {Cdist : ℝ≥0} {εR : ℝ}
    {T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εR}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    (hbad : ¬ SurgeryParamCompat_P6PC (chainDiagonal_C11A T.toChain) 2)
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) (a₀ : ℝ) :
    ¬ ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ →
      Ctime = p6CtimeHN_CHN.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀ := by
  rintro ⟨Θ, hΘ⟩
  have hpc := (hΘ (T₀ := Θ) rfl rfl rfl rfl rfl (fun _ => le_rfl)).1
  exact hbad (paramCompat_of_eqOn_P6SS hpc fun t ht => ⟨(hq t ht).1.symm, (hq t ht).2.symm⟩)

end ObservedHistory

/-! ## (F) εP6 选择子相容 -/

/-- **新 `_hTRs` 的 modelAccuracy 上界为正（`_V2J`）**。 -/
theorem hTRs_accBound_pos_V2J (P : OrientedThreeStage.{u}) (Γ Γf : ClosedBirthConstants) :
    0 < min (min (εSel_W9S.{u} Γ Γf) (Classical.choose hTRs_of_driver_gate_hcol_HCTD_CHN_HPC.{u}))
      (min GC.LongTime.Ch11.εProf_C11E.{u} (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon
        (GC.LongTime.Ch11.chainC1_C11KD Γf) (GC.LongTime.Ch11.chainC2_C11KD Γf) P)) :=
  lt_min (lt_min (εSel_pos_W9S.{u} Γ Γf)
      (Classical.choose_spec hTRs_of_driver_gate_hcol_HCTD_CHN_HPC.{u}).1)
    (lt_min GC.LongTime.Ch11.εProf_pos_C11E.{u} (GC.LongTime.Ch11.epsilon0_pos_C11FR.{u} _ _ _ _))

/-- **正例（`_V2J`）**：存在正 accuracy 同时满足新 `_hTRs` 上界与 hres 槽 `≤ εSel_W9S`。 -/
theorem exists_acc_V2J (P : OrientedThreeStage.{u}) (Γ Γf : ClosedBirthConstants) :
    ∃ a : ℝ, 0 < a ∧
      a ≤ min (min (εSel_W9S.{u} Γ Γf)
          (Classical.choose hTRs_of_driver_gate_hcol_HCTD_CHN_HPC.{u}))
        (min GC.LongTime.Ch11.εProf_C11E.{u} (GC.LongTime.Ch11.epsilon0_C11FR Γf.epsilon
          (GC.LongTime.Ch11.chainC1_C11KD Γf) (GC.LongTime.Ch11.chainC2_C11KD Γf) P)) ∧
      a ≤ εSel_W9S.{u} Γ Γf :=
  ⟨_, hTRs_accBound_pos_V2J P Γ Γf, le_rfl, (min_le_left _ _).trans (min_le_left _ _)⟩

/-- consumer：hsepX 缺口三合取与充分性数值核同时可用。 -/
example : (∀ n : ℕ, (n : ℝ) + 1 ≤ gapR_V2J n) ∧
    (1 : ℝ) < (1 / 2) ^ 2 * ((1 / 10) ^ 2)⁻¹ := by
  refine ⟨hsepX_gap_witness_V2J.1, ?_⟩
  exact scale_ratio_V2J (δ := 1 / 2) (ρe := 1) (ρT := 1 / 2) (r := 1 / 10) (R := 1)
    (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
