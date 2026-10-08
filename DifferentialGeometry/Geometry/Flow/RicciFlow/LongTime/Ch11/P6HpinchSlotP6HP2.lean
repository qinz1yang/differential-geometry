import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationResidueP6HP2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDGateP6F4

/-!
# HIPROP2 G2：`hpinch` 槽（late 窗 `∩ Ici (1/2)` 形）⇐ HIPROP + G1（O-CH11-HIPROP2，后缀 `_P6HP2`）

R-C11-19 Q1：`hpinch` 未付 = HIPROP 的初始输入、重标度后一致下界、实际 FOOT3 接线。
**槽形问题**：HP6B2 v2（`P6HP6bAssemblyV2P6HPB2` l.1209–1263）与 FOOT4 gate（`P6TerminalBCDGateP6F4`
l.149–186）的 `hpinch` 槽要求全事件、**全 slab** `Ico (time i'.castSucc) (time i'.succ)`，且 `phi` 对一切
`c k` 一致。`rescale_P6N c` 下 HI 参数 = `a₀/c + τ`，首 slab `τ = 0` 处无一致下界（初始度量某点负截面曲率 ⇒
`c → ∞` 时任何固定 admissible `phi` 失效），所以全 slab 槽**不能**由 HI 传播生产（lead 裁定：不改原文件，走孪生）。
本文件给 late 窗形：
* **`hpinch_slot_of_HIProp_P6HP2`**（PROVISIONAL[`hinit`, `hrecT`]）：∃ admissible `phi`，
  `hpinch_core_of_HIProp_P6HP2` = 无条件核；槽形
  (1) gate / v2 `hpinch` 槽逐字、只把 slab 换成 `Ico (..) (..) ∩ Ici (1 / 2)`（结论对一切 `k` 成立，前提不用）；
  (2) final 侧（T1      (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
        (s : ℕ → ℝ) (G : ∀ k, (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).stage
          (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)).IncomingSlab
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k)),
        (∀ k, (G k).flow.base.metric (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) =
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).initialMetric
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) →
        ∀ k, Perelman.PhiAlmostNonnegative (G k).flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k) ∩
            Ici (1 / 2)) phi) `hpinchF` 同形）：重标度族接在 last 上的任意 IncomingSlab ∩ `Ici (1 / 2)`，同一 `phi`。
  输入 = 原尺度 `F.tower.history n` 的初始 HI（`hinit`：逐 `n` 的 `a₀ > 0`，**不要求一致**）与全事件 records
  （`hrecT`）；两者 = hgapJ 合同已列的 `0 < a₀ ∧ hHI` 与 `Nonempty (∀ n i, GeometricCutoffRecord ..)`（逐 `n` 版）。
  `phi` 只依赖常数 `1/2`（G1 `hpinch_rescaled_const_P6HP2`）。
* consumer `hpinch_slot_threshold_P6HP2`：把槽喂成 FOOT3 kernel 实际用的形（records 阈值 `T₀` 抬到
  `max T₀ (1/2)` 后的 `∩ Ici (max T₀ (1/2))` pinching）。
gate 孪生（`∩ Ici (1/2)` 槽喂 FOOT3 kernel 孪生）见 G3 `P6HpinchGateLateP6HP2`。
陈述由 build-logs/scratch/O-CH11-HIPROP2/gen/gen_g2.py 从 gate l.150–186 逐字抽取
（只改首行括号与最后一行 slab）生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory

/-- **核（`_P6HP2`，PROVISIONAL[`hinit`, `hrecT`]）**：无条件形——∃ admissible `phi`（只依赖 `1/2`），对一切
`ind c hc k`，重标度族 `Kh k` 的全部 event slab ∩ `Ici (1/2)` 与 final 侧任意 IncomingSlab
∩ `Ici (1/2)` φ-pinched。 -/
theorem hpinch_core_of_HIProp_P6HP2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hinit : ∀ n, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ x,
      InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hrecT : ∀ n, ∃ pF : CutoffParameters,
      Nonempty (∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i pF)) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ)
        (i' : Fin ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.eventCount),
        Perelman.PhiAlmostNonnegative
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.event i').incoming.flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.castSucc)
            (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.succ) ∩
            Ici (1 / 2)) phi) ∧
      (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
        (s : ℕ → ℝ) (G : ∀ k, (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).stage
          (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)).IncomingSlab
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k)),
        (∀ k, (G k).flow.base.metric (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) =
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).initialMetric
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) →
        ∀ k, Perelman.PhiAlmostNonnegative (G k).flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k) ∩
            Ici (1 / 2)) phi) := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_rescaled_late_P6HP2.{u} (T₁ := 1 / 2) (by norm_num)
  choose a₀ ha₀ hHI using hinit
  choose pF hpF using hrecT
  have recordsF : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i (pF n) :=
    fun n => (hpF n).some
  have hK := fun (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) =>
    hP (fun k => F.tower.history (ind k)) c hc (fun k => pF (ind k)) (fun k => recordsF (ind k))
      (fun k => a₀ (ind k)) (fun k => ha₀ (ind k)) (fun k => hHI (ind k)) (fun _ => 1 / 2)
      (fun _ => le_rfl)
  exact ⟨Phi, hPhi, fun ind c hc k i' => (hK ind c hc).1 k i',
    fun ind c hc s G hG k => (hK ind c hc).2 s G hG k⟩

/-- **`hpinch` 槽 late 窗形（`_P6HP2`，PROVISIONAL[`hinit`, `hrecT`]）**：见文件头。 -/
theorem hpinch_slot_of_HIProp_P6HP2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hinit : ∀ n, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ x,
      InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hrecT : ∀ n, ∃ pF : CutoffParameters,
      Nonempty (∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i pF)) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
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
        ∀ᶠ k in atTop, ∀ i' : Fin (Kh k).eventCount,
          Perelman.PhiAlmostNonnegative ((Kh k).event i').incoming.flow
            (Ico ((Kh k).time i'.castSucc) ((Kh k).time i'.succ) ∩ Ici (1 / 2)) phi) ∧
      (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
        (s : ℕ → ℝ) (G : ∀ k, (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).stage
          (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)).IncomingSlab
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k)),
        (∀ k, (G k).flow.base.metric (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) =
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).initialMetric
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) →
        ∀ k, Perelman.PhiAlmostNonnegative (G k).flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).time
            (Fin.last ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).eventCount)) (s k) ∩
            Ici (1 / 2)) phi) := by
  obtain ⟨Phi, hPhi, hev, hfin⟩ := hpinch_core_of_HIProp_P6HP2 F hinit hrecT
  refine ⟨Phi, hPhi, ?_, hfin⟩
  intro ind c hc
  intros
  exact Eventually.of_forall fun k i' => hev ind c hc k i'

/-- **consumer（`_P6HP2`，PROVED ⇐ 槽）**：槽的 `∩ Ici (1/2)` pinching ⇒ FOOT3 kernel 在 records 阈值抬到
`max T₀ (1/2)` 后实际要的 `∩ Ici (max T₀ (1/2))` pinching（单个 history / 任意 `T₀`）。 -/
theorem hpinch_slot_threshold_P6HP2 {Kh : ObservedHistory.{u}} {phi : ℝ → ℝ}
    (h : ∀ i' : Fin Kh.eventCount, Perelman.PhiAlmostNonnegative (Kh.event i').incoming.flow
      (Ico (Kh.time i'.castSucc) (Kh.time i'.succ) ∩ Ici (1 / 2)) phi) (T₀ : ℝ) :
    ∀ i' : Fin Kh.eventCount, Perelman.PhiAlmostNonnegative (Kh.event i').incoming.flow
      (Ico (Kh.time i'.castSucc) (Kh.time i'.succ) ∩ Ici (max T₀ (1 / 2))) phi :=
  fun i' t ht => h i' t ⟨ht.1, (le_max_right T₀ (1 / 2)).trans ht.2⟩

/-- consumer example：核 `hpinch_core_of_HIProp_P6HP2` 的 φ 喂 `hpinch_slot_threshold_P6HP2`
（任意 `ind c k`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (hinit : ∀ n, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ x,
      InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hrecT : ∀ n, ∃ pF : CutoffParameters,
      Nonempty (∀ i, GeometricCutoffRecord (F.tower.history n).toHistory i pF))
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ) (T₀ : ℝ) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      ∀ i' : Fin ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.eventCount,
        Perelman.PhiAlmostNonnegative
          (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.event i').incoming.flow
          (Ico (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.castSucc)
            (((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory.time i'.succ) ∩
            Ici (max T₀ (1 / 2))) phi := by
  obtain ⟨phi, hphi, hev, -⟩ := hpinch_core_of_HIProp_P6HP2 F hinit hrecT
  exact ⟨phi, hphi, hpinch_slot_threshold_P6HP2 (hev ind c hc k) T₀⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
