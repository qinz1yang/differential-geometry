import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HsepXParamCompatP6JG3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CutTubeObstructionCXHB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV2P6HPB2

/-!
# `hscaleSep` ⇐ J10GEN3 G2 `hsepX`（O-CH11-HSCALESEP G1，后缀 `_P6SS`）

HP6B2 v2 的 `hscaleSep` 槽（`P6HP6bAssemblyV2P6HPB2.lean:1489–1543`）结论是
`∀ QA > 0, …, ∀ᶠ k, ∃ pp (Rc : GeometricCutoffRecord (Kh k) (i k) pp), (∀ j, δ_j ≤ 1/2) ∧
∀ j, QA·R_k < (1 − 4323 δ_j)·(Rc.neck j).scale`；J10GEN3 G2 的 `hsepX`
（`hsepX_of_paramCompat_P6JG3`，`∀ M, ∀ᶠ n, ∀ e he b, a n < time →
M·R n < (records.static b).neck.scale`）
管的是 **recentered static cap neck**（retained boundary `b`）。R-C11-19 Q1 标 OPEN 的适配关系在此核清：
* **neck 不同**：槽要 tube neck `(Rc.neck j).scale`（∀ tube index `j`）。桥 = `one_retained_side`
  （每个 `j` 有 retained 侧 `b`，`b.1.1 = j`，`exists_retainedSide_CXHB`）+ `recenter_scale_comparison`
  （`|static/tube − 1| ≤ Λ δ_j`，`Λδ ≤ 1/2` ⇒ `static ≤ (3/2)·tube`）。取 `M := 3·QA`。
* **常数**：`1 − 4323 δ > 0` 要 `δ < 1/4323`（"δ ≤ 1/2 时为正"不成立）；这里要 `4323·δ(σ) ≤ 1/2`，由
  `hsepX` 自己的窗口 binder `hδ` 取 `Qb := 8646²/8`（`8 Qb δ² ≤ 1` ⇒ `8646 δ ≤ 1`）付，**不加 binder**。
* **records 范围**：槽的 `∃ pp Rc` 自由（不需与 `hrecords` 同一 witness）；要 records-X 家族、
  `T₀X ≤ time (i k).succ`（eventually）与 `a < time (i k).succ`（eventually）。

本文件：
* `static_scale_le_tube_P6SS` / `tube_scaleSep_of_static_P6SS`（PROVED，单 record 核）；
* **`hscaleSep_of_hsepX_P6SS`（PROVED，适配引理）**：`hsepX`（∀ M）+ 同一 `hδ` + 两条 eventual 范围
  ⇒ 槽结论形；
* `hscaleSep_ev_of_paramCompat_witness_P6SS`（PROVISIONAL[`hpc` / `hTn` / `hδ`]）：接
  `hsepX_of_paramCompat_witness_P6JG3`；
* **`hscaleSep_body_of_paramCompat_P6SS`**（PROVISIONAL[`hpc` / `hTn`]）：结论 = 槽体（`∀ QA` 起）**逐字**；
  records-X 由 S14 `LateLinkedRecordsSupply_C11E F q` 经 `recordsKRescale_P6X3` 构造
  （`T₀X := max 1 (T/c)`），
  窗口 `hδ` 由 S1 形 `hδq : q.delta → 0` + S14 的 `p.recenterConstant = q.recenterConstant` + K 窗
  `c·aSeed ≥ (k+1)/2` **证出**（不再是独立 binder）；`T₀X ≤ σ`、`aSeed < σ`、`R → ∞` 由槽前件证出；
* **`hscaleSep_slot_of_paramCompat_P6SS`**：结论 = HP6B2 v2 `hscaleSep` 槽 **逐字**（前缀
  `pB Γ Γf … Ctime` 起），四个 binder 各带同一前缀；consumer `example` 把它经 named argument 喂进
  `hP6bTwoLevelTime_of_slots_v2_P6HPB2`；
* `tnRow_of_sigmaCeil_P6SS`（PROVED）：σ 处 ceiling（S-CH11-SCALESEP `hceil`）+ `ρ` antitone ⇒ Tn 行。
binder 来源：`hpc` = PARAMCOMPAT 主合同 `SurgeryParamCompat_P6PC q 2`（owner = chain / successor 存在性，
链上形 `paramCompat_of_chain_P6PC` 只剩相邻比 `hstep`）；`hTn` = Tn 行 `R_k ≤ ρ̃_k(Tn_k)⁻²`（selection 输出形；
在槽的全称族上 ⇐ σ 处 ceiling）。陈述由 `build-logs/scratch/O-CH11-HSCALESEP/gen.py` 从 HP6B2 槽逐字生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B)

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- tube `j` 的 neck scale 为正（`scale_eq` + `nominal_pos`）。 -/
theorem neck_scale_pos_P6SS (Rc : GeometricCutoffRecord H i pp)
    (j : (H.event i).transition.trace.tubes.Index) : 0 < (Rc.neck j).scale := by
  rw [Rc.scale_eq]
  exact inv_pos.mpr (pow_pos (Rc.nominal_pos _) 2)

/-- **static ≤ (3/2)·tube（PROVED）**：`Λ·δ(t) ≤ 1/2`（`t = time i.succ`）⇒ retained boundary `b` 的
recentered static neck scale `≤ (3/2)·(Rc.neck b.1.1).scale`
（`recenter_scale_comparison` + `delta_le`）。 -/
theorem static_scale_le_tube_P6SS (Rc : GeometricCutoffRecord H i pp)
    (hrec : pp.recenterConstant * pp.delta (H.time i.succ) ≤ 1 / 2)
    (b : (H.event i).RetainedBoundaryIndex) :
    (Rc.static b).neck.scale ≤ 3 / 2 * (Rc.neck b.1.1).scale := by
  have hC : 0 ≤ pp.recenterConstant := by linarith [pp.recenterConstant_ge_four]
  have hpos := Rc.neck_scale_pos_P6SS b.1.1
  have h1 : pp.recenterConstant * Rc.delta b.1.1 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (Rc.delta_le b.1.1) hC).trans hrec
  have h2 := (abs_le.mp ((Rc.recenter_scale_comparison b).trans h1)).2
  have h3 : (Rc.static b).neck.scale / (Rc.neck b.1.1).scale ≤ 3 / 2 := by linarith
  rw [div_le_iff₀ hpos] at h3
  exact h3

/-- **单 record 核（PROVED）**：`Λδ(t) ≤ 1/2`、`4323·δ(t) ≤ 1/2`、所有 retained `b` 上
`3·QA·R < static(b).scale` ⇒ 槽的 record 部分 `(∀ j, δ_j ≤ 1/2) ∧ ∀ j, QA·R < (1 − 4323 δ_j)·tube_j`。 -/
theorem tube_scaleSep_of_static_P6SS (Rc : GeometricCutoffRecord H i pp) {QA R : ℝ}
    (hrec : pp.recenterConstant * pp.delta (H.time i.succ) ≤ 1 / 2)
    (hsmall : 4323 * pp.delta (H.time i.succ) ≤ 1 / 2)
    (hsep : ∀ b, 3 * QA * R < (Rc.static b).neck.scale) :
    (∀ j, Rc.delta j ≤ 1 / 2) ∧ ∀ j, QA * R < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  have hd0 : 0 < pp.delta (H.time i.succ) := pp.delta_pos _ (H.time_nonneg i.succ)
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := Rc.delta_le j
    linarith
  · obtain ⟨s, hs⟩ := Rc.exists_retainedSide_CXHB j
    have hle : (Rc.static ⟨(j, s), hs⟩).neck.scale ≤ 3 / 2 * (Rc.neck j).scale :=
      Rc.static_scale_le_tube_P6SS hrec ⟨(j, s), hs⟩
    have hsp := hsep ⟨(j, s), hs⟩
    have hpos := Rc.neck_scale_pos_P6SS j
    have hdj := Rc.delta_le j
    have hfac : 1 / 2 ≤ 1 - 4323 * Rc.delta j := by linarith
    have hm : 1 / 2 * (Rc.neck j).scale ≤ (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
      mul_le_mul_of_nonneg_right hfac hpos.le
    linarith

end GeometricCutoffRecord

/-- 算术：`8·(8646²/8)·d² ≤ 1`、`0 ≤ d` ⇒ `4323·d ≤ 1/2`。 -/
theorem small_of_sq_le_P6SS {d : ℝ} (hd0 : 0 ≤ d) (h : 8 * (8646 ^ 2 / 8) * d ^ 2 ≤ 1) :
    4323 * d ≤ 1 / 2 := by
  nlinarith

/-- 算术：`0 ≤ d ≤ 1`、`d ≤ 1/(2(Λ + 8Qb + 1))` ⇒ `Λd ≤ 1/2 ∧ 8·Qb·d² ≤ 1`。 -/
theorem small_of_le_eta_P6SS {C Qb d : ℝ} (hC : 0 ≤ C) (hQb : 0 ≤ Qb) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hd : d ≤ 1 / (2 * (C + 8 * Qb + 1))) : C * d ≤ 1 / 2 ∧ 8 * Qb * d ^ 2 ≤ 1 := by
  have hpos : 0 < 2 * (C + 8 * Qb + 1) := by positivity
  have h := (le_div_iff₀ hpos).mp hd
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hq : Qb * d ^ 2 ≤ Qb * d := mul_le_mul_of_nonneg_left hd2 hQb
  have hqd : 0 ≤ Qb * d := mul_nonneg hQb hd0
  constructor <;> nlinarith

/-- **适配引理 `hscaleSep_of_hsepX_P6SS`（PROVED）**：J10GEN3 G2 的 `hsepX`（`∀ M`，static neck）+ **同一**
窗口 binder `hδ`（`Λδ ≤ 1/2 ∧ 8·Qb·δ² ≤ 1`）+ 选定 event `i n` 的两条 eventual 范围（`T₀X ≤ time`、
`a < time`）⇒ HP6B2 `hscaleSep` 槽的结论形（tube neck，`∀ QA > 0`）。取 `M := 3·QA`、`Qb := 8646²/8`。 -/
theorem hscaleSep_of_hsepX_P6SS {Hs : ℕ → ObservedHistory.{u}} {pX : ℕ → CutoffParameters}
    {T₀X a R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (pX n))
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, a n < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → a n < (Hs n).time e.succ →
      (pX n).recenterConstant * (pX n).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (pX n).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (i : ∀ n, Fin (Hs n).eventCount)
    (hT₀ : ∀ᶠ n in atTop, T₀X n ≤ (Hs n).time (i n).succ)
    (hwin : ∀ᶠ n in atTop, a n < (Hs n).time (i n).succ) :
    ∀ QA : ℝ, 0 < QA → ∀ᶠ n in atTop, ∃ (pp : CutoffParameters)
      (Rc : GeometricCutoffRecord (Hs n) (i n) pp),
      (∀ j, Rc.delta j ≤ 1 / 2) ∧ ∀ j, QA * R n < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro QA _
  filter_upwards [hsepX (3 * QA), hδ (8646 ^ 2 / 8) (by positivity), hT₀, hwin] with n hs hd hT hw
  refine ⟨pX n, recordsX n (i n) hT, ?_⟩
  have hdn := hd (i n) hT hw
  have hd0 : 0 ≤ (pX n).delta ((Hs n).time (i n).succ) :=
    ((pX n).delta_pos _ ((Hs n).time_nonneg (i n).succ)).le
  exact (recordsX n (i n) hT).tube_scaleSep_of_static_P6SS hdn.1 (small_of_sq_le_P6SS hd0 hdn.2)
    (fun b => hs (i n) hT b hw)

/-- **family consumer（PROVISIONAL[`hpc` / `hTn` / `hδ`]）**：J10GEN3 G2 同一 witness 形
`hsepX_of_paramCompat_witness_P6JG3` 喂适配引理 ⇒ 槽结论形。 -/
theorem hscaleSep_ev_of_paramCompat_witness_P6SS {Hs : ℕ → ObservedHistory.{u}}
    {p q : ℕ → CutoffParameters} {θ : ℝ} (hθ : 0 ≤ θ) {T₀X a Tn R : ℕ → ℝ}
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (p n))
    (hpq : ∀ n, (p n).delta = (q n).delta ∧ (p n).neckRadius = (q n).neckRadius)
    (hpc : ∀ n, SurgeryParamCompat_P6PC (q n) θ) (hTn0 : ∀ n, 0 ≤ Tn n)
    (hwin : ∀ n, Tn n ≤ θ * a n) (hTn : ∀ n, R n ≤ ((p n).neckRadius (Tn n) ^ 2)⁻¹)
    (hδ : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ n in atTop, ∀ e : Fin (Hs n).eventCount,
      T₀X n ≤ (Hs n).time e.succ → a n < (Hs n).time e.succ →
      (p n).recenterConstant * (p n).delta ((Hs n).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (p n).delta ((Hs n).time e.succ) ^ 2 ≤ 1)
    (hRlim : Tendsto R atTop atTop) (i : ∀ n, Fin (Hs n).eventCount)
    (hT₀ : ∀ᶠ n in atTop, T₀X n ≤ (Hs n).time (i n).succ)
    (hwinI : ∀ᶠ n in atTop, a n < (Hs n).time (i n).succ) :
    ∀ QA : ℝ, 0 < QA → ∀ᶠ n in atTop, ∃ (pp : CutoffParameters)
      (Rc : GeometricCutoffRecord (Hs n) (i n) pp),
      (∀ j, Rc.delta j ≤ 1 / 2) ∧ ∀ j, QA * R n < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale :=
  hscaleSep_of_hsepX_P6SS recordsX
    (hsepX_of_paramCompat_witness_P6JG3 hθ recordsX hpq hpc hTn0 hwin hTn hδ hRlim) hδ i hT₀ hwinI

/-- **Tn 行 ⇐ σ 处 ceiling（PROVED）**：`ρ` antitone（合同第一项）+ `σ ≤ Tn` ⇒
`R ≤ ρ(σ)⁻² → R ≤ ρ(Tn)⁻²`。即 Tn 行比 S-CH11-SCALESEP 的 `hceil` 弱。 -/
theorem tnRow_of_sigmaCeil_P6SS {q : CutoffParameters} {θ : ℝ} (hpc : SurgeryParamCompat_P6PC q θ)
    {σ Tn R : ℝ} (hσ0 : 0 ≤ σ) (hsT : σ ≤ Tn) (hceil : R ≤ (q.neckRadius σ ^ 2)⁻¹) :
    R ≤ (q.neckRadius Tn ^ 2)⁻¹ := by
  have hT0 : 0 ≤ Tn := hσ0.trans hsT
  have hle : q.neckRadius Tn ≤ q.neckRadius σ := hpc.1 (mem_Ici.mpr hσ0) (mem_Ici.mpr hT0) hsT
  have hpos := q.neckRadius_pos Tn hT0
  exact hceil.trans (inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2))

/-- **槽体（PROVISIONAL[`hpc` / `hTn`]）**：结论 = HP6B2 `hscaleSep` 槽从 `∀ QA` 起**逐字**（固定 `F q ε C1 C2
Ctime`）。records-X ⇐ S14（`recordsKRescale_P6X3`，`T₀X := max 1 (T/c)`）；窗口 `hδ` ⇐ `hδq` + S14 的
`recenterConstant` 等式 + `c·aSeed ≥ (k+1)/2`；`T₀X ≤ σ`、`aSeed < σ`、`R → ∞`、`Tn ≤ 2·aSeed` ⇐ 槽前件。 -/
theorem hscaleSep_body_of_paramCompat_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hpc : SurgeryParamCompat_P6PC q 2)
    (hTn :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k)) ^ 2)⁻¹) :
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro QA hQA ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hTnK := hTn ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood hwin hwin' hroom hradii i hi
  obtain ⟨T, hT⟩ := hS14 0 1 0 one_pos
  choose p hpd hpn hpf hpr hD hζ hm records hlink using hT
  have hpq : ∀ k,
      ((p (ind k)).rescale_P6N (c k) (hc k)).delta = (q.rescale_P6N (c k) (hc k)).delta ∧
      ((p (ind k)).rescale_P6N (c k) (hc k)).neckRadius =
        (q.rescale_P6N (c k) (hc k)).neckRadius := fun k => by
    refine ⟨funext fun t => ?_, funext fun t => ?_⟩
    · change (p (ind k)).delta (c k * t) = q.delta (c k * t)
      rw [hpd]
    · change (p (ind k)).neckRadius (c k * t) / Real.sqrt (c k) =
        q.neckRadius (c k * t) / Real.sqrt (c k)
      rw [hpn]
  have hwinK : ∀ k, (Tn k : ℝ) ≤ 2 * (aSeed k : ℝ) := fun k =>
    window_le_two_mul_P6PC (hclock k) (h1 k) le_rfl
  have hca : ∀ k : ℕ, ((k : ℝ) + 1) / 2 ≤ c k * (aSeed k : ℝ) := fun k => by
    have hm2 := mul_le_mul_of_nonneg_left (hwinK k) (hc k).le
    have hTck := hTc k
    linarith
  have hcaT : Tendsto (fun k => c k * (aSeed k : ℝ)) atTop atTop :=
    tendsto_atTop_mono hca
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_div_const two_pos)
  have hδK : ∀ Qb : ℝ, 0 ≤ Qb → ∀ᶠ k in atTop, ∀ e : Fin (Kh k).eventCount,
      max 1 (T / c k) ≤ (Kh k).time e.succ → (aSeed k : ℝ) < (Kh k).time e.succ →
      ((p (ind k)).rescale_P6N (c k) (hc k)).recenterConstant *
          ((p (ind k)).rescale_P6N (c k) (hc k)).delta ((Kh k).time e.succ) ≤ 1 / 2 ∧
        8 * Qb * ((p (ind k)).rescale_P6N (c k) (hc k)).delta ((Kh k).time e.succ) ^ 2 ≤ 1 := by
    intro Qb hQb
    have hC : 0 ≤ q.recenterConstant := by linarith [q.recenterConstant_ge_four]
    have hη : (0 : ℝ) < 1 / (2 * (q.recenterConstant + 8 * Qb + 1)) := by positivity
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hη))
    filter_upwards [hcaT.eventually_ge_atTop B] with k hk e _ hae
    have hτ0 : 0 ≤ (Kh k).time e.succ := (Kh k).time_nonneg e.succ
    have hcτ : B ≤ c k * (Kh k).time e.succ :=
      hk.trans (mul_le_mul_of_nonneg_left hae.le (hc k).le)
    have hct0 : 0 ≤ c k * (Kh k).time e.succ := mul_nonneg (hc k).le hτ0
    change (p (ind k)).recenterConstant * (p (ind k)).delta (c k * (Kh k).time e.succ) ≤ 1 / 2 ∧
      8 * Qb * (p (ind k)).delta (c k * (Kh k).time e.succ) ^ 2 ≤ 1
    rw [hpr, hpd]
    exact small_of_le_eta_P6SS hC hQb (q.delta_pos _ hct0).le (q.delta_lt_one _ hct0).le
      (hB _ hcτ)
  have hcs : Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) hcaT
    rw [← hi k]
    exact mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr (has k)) (hc k).le
  have hT₀ : ∀ᶠ k in atTop, max 1 (T / c k) ≤ (Kh k).time (i k).succ := by
    filter_upwards [hcs.eventually_ge_atTop T] with k hk
    refine max_le ?_ ?_
    · rw [← hi k]
      exact (h1 k).trans (Subtype.coe_le_coe.mpr (has k))
    · rw [div_le_iff₀ (hc k), mul_comm]
      exact hk
  have hwinI : ∀ᶠ k in atTop, (aSeed k : ℝ) < (Kh k).time (i k).succ := by
    filter_upwards [hwin 1 one_pos] with k hk
    rw [← hi k]
    have : 0 < 1 / R k := one_div_pos.mpr (hRpos k)
    linarith
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hTnK' : ∀ k, R k ≤ (((p (ind k)).rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹ :=
    fun k => by
      rw [(hpq k).2]
      exact hTnK k
  exact hscaleSep_ev_of_paramCompat_witness_P6SS (Hs := Kh)
    (q := fun k => q.rescale_P6N (c k) (hc k)) (θ := 2) (by norm_num)
    (T₀X := fun k => max 1 (T / c k)) (a := fun k => (aSeed k : ℝ)) (Tn := fun k => (Tn k : ℝ))
    (fun k e he => (F.tower.history (ind k)).recordsKRescale_P6X3 (hc k) (records (ind k)) e he)
    hpq (fun k => paramCompat_rescale_P6PC hpc (c k) (hc k)) (fun k => (Tn k).2.1) hwinK hTnK'
    hδK hRlim i hT₀ hwinI QA hQA

/-- **HP6B2 `hscaleSep` 槽（PROVISIONAL[`hpc` / `hTn`]）**：结论 = `P6HP6bAssemblyV2P6HPB2.lean:1490–1543`
**逐字**；四个 binder 带同一前缀（`hS14` = S14、`hδq` = S1 形 `q.delta → 0`、`hpc` = PARAMCOMPAT 主合同、
`hTn` = Tn 行）。逐前缀调用 `hscaleSep_body_of_paramCompat_P6SS`。 -/
theorem hscaleSep_slot_of_paramCompat_P6SS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hS14 :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      Tendsto q.delta atTop (𝓝 0))
    (hpc :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      SurgeryParamCompat_P6PC q 2)
    (hTn :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k)) ^ 2)⁻¹) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ QA : ℝ, 0 < QA →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ j, Rc.delta j ≤ 1 / 2) ∧
          ∀ j, QA * R k < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  exact hscaleSep_body_of_paramCompat_P6SS
    (hS14 hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hδq hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hpc hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord)
    (hTn hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord hε hC1 hC2 hCt)

/-- **consumer（G1）**：本文件的槽产出经 named argument 直接喂进 HP6B2 v2 装配
`hP6bTwoLevelTime_of_slots_v2_P6HPB2`（类型检查 = 槽形逐字一致）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 hδq hpc hTn =>
  ObservedHistory.hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6
    (hscaleSep := hscaleSep_slot_of_paramCompat_P6SS (P := P) (g := g) εP6 hS14 hδq hpc hTn)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
