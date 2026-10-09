import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransESmallDeltaCXHB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BadInstC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6C11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E

/-!
# δ-small late records 的 producer（O-CH11-HRECDELTA G1/G2，后缀 `_P6HD`）

CX-HTUBE2 G3 的唯一 open 合同 `SmallDeltaLateRecords_CXHB2 F eps`（`P6HtransESmallDeltaCXHB2.lean` :40）
在这里由两条**树内已有**的事实付掉，**不加新 binder**：

* records 存在式 = P5L supply `LateLinkedRecordsSupply_C11E F q`（S14；HREC6 `hrec_of_P5L_P6H6`
  用的同一供给）：晚期 event 有 record，参数 `p` 满足 `p.delta = q.delta`；
* δ 衰减 = `Tendsto q.delta atTop (𝓝 0)`（astra tuple / SCRS 第 4 组的 `hδlim`；GAPTOP6 / GAPTOP7B 顶层
  在同一 `(F, q)` 上与 `hlate` 一起由 `exists_surgery_with_retained_raw_caps` 产出）。

机制：records 经 `rescale_P6M` 到 `Kh k`，参数 `pp = p.rescale_P6N (c k)`，`pp.delta t = p.delta (c k · t)`，
所以 `pp.delta (Kh.time (i k).succ) = q.delta (Ho.time (i k).succ)`；lateness 前提（与 `hcapWL` 同款
`Tendsto (c k · Kh.time (i k).succ) atTop atTop`，不另造）给出 Ho 时间 `→ ∞`，δ 衰减即得 `≤ eps`。

* **G1** `smallDeltaLateRecords_of_P5L_P6HD`：`hP5L` + `hδq` ⇒ 合同，∀ `eps > 0`（PROVED）。
  SCRS 孪生 `smallDeltaLateRecords_of_SCRS_P6HD`（`F.tower = T.toChain.tower`，经 tower-congruence
  `smallDeltaLateRecords_congr_tower_P6HD`）。
  `htransE_of_P5L_P6HD` / `hbd_stage_late_of_P5L_P6HD`：CXHB2 两个定理的陈述**逐字**，只把
  `(eps, hSD, heps, hδ)` 四个 binder 换成 `(qc, hP5L, hδq)`（`eps := smallDeltaEps_P6HD C1₁ C2₁` 在证明内取；
  由 `build-logs/scratch/O-CH11-HRECDELTA/gen.py` 从源文本抽取并断言其余字节相同）。
* **G2** `eps_Γ = epsDeltaBad_P6HD Γ = min (1/12) (1/(10·c·√c))`，`c = c(Γ) = p6BadC_C11G2 Γ`
  （`c^{3/2} = c·√c`）：`smallDeltaLateRecords_bad_P6HD` 给出合同 + 两个数值门槛；文件末的 `example`
  在 GAPTOP7B 的 c(Γ) 元组处喂 `htransE_of_smallDelta_CXHB2`，并与 `htrans_bad_C11G7B` 经
  `htransE_of_htrans_P6HB4` 得到的 htransE **同型对照**（同一常数，类型由同一 `X : Prop` 统一），
  再喂 `hbd_stage_late_smallDelta_CXHB2`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-! ## 1. G1：P5L records + δ 衰减 ⇒ `SmallDeltaLateRecords_CXHB2` -/

/-- **G1（PROVED）**：P5L supply `LateLinkedRecordsSupply_C11E F q`（records 的 `p.delta = q.delta`）与
`Tendsto q.delta atTop (𝓝 0)` ⇒ 对任意 `eps > 0`，合同 `SmallDeltaLateRecords_CXHB2 F eps` 成立。
record 取 `rescale_P6M`（同 `hrec_of_P5L_P6H6`），`pp.delta (Kh.time) = q.delta (Ho.time)`。 -/
theorem smallDeltaLateRecords_of_P5L_P6HD {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) {eps : ℝ} (heps : 0 < eps) :
    SmallDeltaLateRecords_CXHB2 F eps := by
  intro ind c hc Kh i hlate
  obtain ⟨T, hT⟩ := hP5L 0 1 0 one_pos
  have hδev : ∀ᶠ t in atTop, q.delta t < eps := hδq.eventually (eventually_lt_nhds heps)
  obtain ⟨T', hT'⟩ := Filter.eventually_atTop.1 hδev
  have hev : ∀ᶠ k in atTop, max T T' ≤ (F.tower.history (ind k)).time (i k).succ := by
    filter_upwards [hlate.eventually_ge_atTop (max T T')] with k hk
    have e : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
      mul_div_cancel₀ _ (hc k).ne'
    exact e ▸ hk
  filter_upwards [hev] with k hk
  obtain ⟨p, hpδ, -, -, -, -, -, -, records, -⟩ := hT (ind k)
  refine ⟨p.rescale_P6N (c k) (hc k),
    (records (i k) ((le_max_left _ _).trans hk)).rescale_P6M (c k) (hc k), ?_⟩
  change p.delta (c k * (Kh k).time (i k).succ) ≤ eps
  have e : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
    mul_div_cancel₀ _ (hc k).ne'
  rw [e, hpδ]
  exact (hT' _ ((le_max_right _ _).trans hk)).le

/-- **tower-congruence**：合同只读 `F.tower`，同 tower 的两个 surgery 等价地满足它。 -/
theorem smallDeltaLateRecords_congr_tower_P6HD {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F F' : GC.Interface.RawSurgery P g} (h : F.tower = F'.tower) {eps : ℝ}
    (hF : SmallDeltaLateRecords_CXHB2 F eps) : SmallDeltaLateRecords_CXHB2 F' eps := by
  obtain ⟨tw, ec⟩ := F
  obtain ⟨tw', ec'⟩ := F'
  change tw = tw' at h
  subst h
  exact hF

/-- `eps` 的标准取法：`min (1/12) (1/(10 · C1₁ · √C2₁))`（满足 `htrans_event_record_CXHB2` 的两个门槛）。 -/
def smallDeltaEps_P6HD (C1₁ C2₁ : ℝ) : ℝ :=
  min (1 / 12) (1 / (10 * C1₁ * Real.sqrt C2₁))

/-- `smallDeltaEps_P6HD` 的三条数值性质：`0 < eps`、`eps < 1/11`、`eps · (10 · C1₁ · √C2₁) ≤ 1`。 -/
theorem smallDeltaEps_spec_P6HD {C1₁ C2₁ : ℝ} (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁) :
    0 < smallDeltaEps_P6HD C1₁ C2₁ ∧ smallDeltaEps_P6HD C1₁ C2₁ < 1 / 11 ∧
      smallDeltaEps_P6HD C1₁ C2₁ * (10 * C1₁ * Real.sqrt C2₁) ≤ 1 := by
  unfold smallDeltaEps_P6HD
  have hs : 0 < Real.sqrt C2₁ := Real.sqrt_pos.mpr (by linarith)
  have hX : 0 < 10 * C1₁ * Real.sqrt C2₁ := mul_pos (mul_pos (by norm_num) (by linarith)) hs
  refine ⟨lt_min (by norm_num) (one_div_pos.mpr hX), (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  exact (le_div_iff₀ hX).mp (min_le_right _ _)

namespace ObservedHistory

/-- **`htransE` producer（无 eps、无 htube）**：`htransE_of_smallDelta_CXHB2` 的陈述逐字，`(eps, hSD, heps, hδ)`
换成 P5L supply `hP5L` + δ 衰减 `hδq`（`eps := smallDeltaEps_P6HD C1₁ C2₁`，G1 付合同）。 -/
theorem htransE_of_P5L_P6HD {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ}
    {qc : CutoffParameters} (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F qc)
    (hδq : Tendsto qc.delta atTop (𝓝 0)) (hε : 0 < ε) (hη₁ : 0 < η₁)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2) :
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          (¬ ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2 q,
            W.capTubeHasNeckChart ε) →
          ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
            (((Kh k).event (i k)).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p',
            W.capTubeHasNeckChart η₁ := by
  have h := smallDeltaEps_spec_P6HD hC1₁ hC2₁
  exact htransE_of_smallDelta_CXHB2 (smallDeltaLateRecords_of_P5L_P6HD hP5L hδq h.1) h.2.1 h.2.2
    hε hη₁ hη hsmall hC1₁ hC2₁ hC1f hC2f hm hm' h1 h2

/-- **consumer（hbd）**：`hbd_stage_late_smallDelta_CXHB2` 的陈述逐字，`(eps, hSD, heps, hδ)` 换成
`(qc, hP5L, hδq)`；证明直接调 CXHB2 consumer，合同由 G1 付。 -/
theorem hbd_stage_late_of_P5L_P6HD {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    (hcapWL : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    (hcenE :
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) (Kh k).horizon) (z : ((Kh k).stageAt t).Carrier),
            (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed k ≤ t) (hvt : t ≤ Tn k),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
                ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k))))
    (hfootE :
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          Nonempty (((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    {qc : CutoffParameters} (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F qc)
    (hδq : Tendsto qc.delta atTop (𝓝 0)) (hε : 0 < ε) (hη₁ : 0 < η₁)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (hC1f : max C1₁ 9 + Real.sqrt C2₁ ≤ C1f) (hC2f : 1200 * C2₁ ≤ C2f) (hm : m ≤ 1 / 20)
    (hm' : m ≤ 1 / (10 * C1₁ * Real.sqrt C2₁)) (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2)
    (hrerunE8 :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) → (∀ k : ℕ, (k : ℝ) + 1 < R k) → False) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
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
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False := by
  have h := smallDeltaEps_spec_P6HD hC1₁ hC2₁
  exact hbd_stage_late_smallDelta_CXHB2 hcapWL hcenE hfootE
    (smallDeltaLateRecords_of_P5L_P6HD hP5L hδq h.1) h.2.1 h.2.2 hε hη₁ hη hsmall hC1₁ hC2₁ hC1f
    hC2f hm hm' h1 h2 hrerunE8

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow

universe u

/-- **SCRS 孪生（PROVED）**：同构造保留供给 `SameConstructionRetentionSupply_C11GT6 T` 的第 4 组 `hδlim` 与
第 5 组 `LateLinkedRecordsSupply_C11E F₀ q₀`（同一 `(F₀, q₀)`）⇒ 任意 `F.tower = T.toChain.tower` 的 surgery
满足合同，∀ `eps > 0`。 -/
theorem smallDeltaLateRecords_of_SCRS_P6HD {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hSCRS : SameConstructionRetentionSupply_C11GT6 T) {F : GC.Interface.RawSurgery P g}
    (hF : F.tower = T.toChain.tower) {eps : ℝ} (heps : 0 < eps) :
    SmallDeltaLateRecords_CXHB2 F eps := by
  obtain ⟨F₀, q₀, _, _, ⟨hTw, -, -⟩, -, -, ⟨-, -, hδlim⟩, ⟨-, -, -, hlate⟩, -, -⟩ := hSCRS
  exact smallDeltaLateRecords_congr_tower_P6HD (hTw.trans hF.symm)
    (smallDeltaLateRecords_of_P5L_P6HD hlate hδlim heps)

/-! ## 2. G2：c(Γ) 元组处的数值实例 -/

/-- **`eps_Γ`**：`smallDeltaEps_P6HD` 在 `C1₁ = C2₁ = c(Γ) = p6BadC_C11G2 Γ` 处（D-15″）。 -/
def epsDeltaBad_P6HD (Γ : ClosedBirthConstants) : ℝ :=
  smallDeltaEps_P6HD (p6BadC_C11G2.{u} Γ) (p6BadC_C11G2.{u} Γ)

/-- 展开式：`eps_Γ = min (1/12) (1/(10 · c · √c))`（`c^{3/2} = c · √c`）。 -/
theorem epsDeltaBad_eq_P6HD (Γ : ClosedBirthConstants) :
    epsDeltaBad_P6HD.{u} Γ =
      min (1 / 12) (1 / (10 * p6BadC_C11G2.{u} Γ * Real.sqrt (p6BadC_C11G2.{u} Γ))) :=
  rfl

/-- **G2（PROVED）**：c(Γ) 处合同 + `htransE_of_smallDelta_CXHB2` 的两个数值门槛
（`eps_Γ < 1/11`、`eps_Γ · (10 · c · √c) ≤ 1`）。 -/
theorem smallDeltaLateRecords_bad_P6HD (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : LateLinkedRecordsSupply_C11E F q) (hδq : Tendsto q.delta atTop (𝓝 0)) :
    SmallDeltaLateRecords_CXHB2 F (epsDeltaBad_P6HD.{u} Γ) ∧ epsDeltaBad_P6HD.{u} Γ < 1 / 11 ∧
      epsDeltaBad_P6HD.{u} Γ * (10 * p6BadC_C11G2.{u} Γ * Real.sqrt (p6BadC_C11G2.{u} Γ)) ≤ 1 := by
  have h := smallDeltaEps_spec_P6HD (one_le_p6BadC_C11G7B.{u} Γ) (one_le_p6BadC_C11G7B.{u} Γ)
  exact ⟨smallDeltaLateRecords_of_P5L_P6HD hP5L hδq h.1, h.2.1, h.2.2⟩

/-- consumer（G2，htransE @ c(Γ)）：G2 喂 `htransE_of_smallDelta_CXHB2`（GAPTOP7B 的 c(Γ) 元组，逐参数同
`htrans_bad_C11G7B`）；与 `htrans_bad_C11G7B` 经 `htransE_of_htrans_P6HB4` 得到的 htransE 由同一
`X : Prop` 统一（同型 = 同一常数）。 -/
example (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{0}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {qc : CutoffParameters} {kk : ℕ} {Ctime : ℝ≥0}
    (hP5L : LateLinkedRecordsSupply_C11E F qc) (hδq : Tendsto qc.delta atTop (𝓝 0))
    (htube : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{0} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    True := by
  have hS := smallDeltaLateRecords_bad_P6HD.{0} Γ hP5L hδq
  have hD := ObservedHistory.htransE_of_smallDelta_CXHB2 (F := F) (Ctime := Ctime) (kk := kk)
    (ε := Γ.epsilon) (C1 := C1P6_C11GT6.{0} p6X1std_C11GT6.{0} Γ)
    (C2 := C2P6_C11GT6.{0} p6X2std_C11GT6.{0} Γ)
    (C1f := max (p6BadC_C11G2.{0} Γ) 9 + Real.sqrt (p6BadC_C11G2.{0} Γ))
    (C2f := 1200 * p6BadC_C11G2.{0} Γ) (m := htransMBad_C11G7B.{0} Γ)
    (η₁ := p6FineEta_C11GT6 Γ.epsilon) (C1₁ := p6BadC_C11G2.{0} Γ) (C2₁ := p6BadC_C11G2.{0} Γ)
    hS.1 hS.2.1 hS.2.2 Γ.epsilon_pos (p6FineEta_pos_C11GT6 Γ.epsilon_pos)
    (thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon) (fineEta_le_bJS_C11CL3 Γ.epsilon)
    (one_le_p6BadC_C11G7B.{0} Γ) (one_le_p6BadC_C11G7B.{0} Γ) le_rfl le_rfl
    (min_le_left _ _) (min_le_right _ _) (hdomL_bad_C11G7B.{0} Γ).1
    (by linarith [(hdomL_bad_C11G7B.{0} Γ).2])
  have hB := ObservedHistory.htransE_of_htrans_P6HB4 (F := F) (Ctime := Ctime) (ε := Γ.epsilon)
    (C1 := C1P6_C11GT6.{0} p6X1std_C11GT6.{0} Γ) (C2 := C2P6_C11GT6.{0} p6X2std_C11GT6.{0} Γ)
    (C1f := max (p6BadC_C11G2.{0} Γ) 9 + Real.sqrt (p6BadC_C11G2.{0} Γ))
    (C2f := 1200 * p6BadC_C11G2.{0} Γ) (m := htransMBad_C11G7B.{0} Γ)
    (η₁ := p6FineEta_C11GT6 Γ.epsilon) (C1₁ := p6BadC_C11G2.{0} Γ) (C2₁ := p6BadC_C11G2.{0} Γ)
    (kk := kk) (htrans_bad_C11G7B.{0} Γ (F := F) (kk := kk) htube)
  exact (fun (X : Prop) (_ _ : X) => trivial) _ hD hB

/-- consumer（G2，hbd @ c(Γ)）：G2 喂 `hbd_stage_late_smallDelta_CXHB2` 的 `(hSD, heps, hδ)` 槽，
其余常数同 GAPTOP7B c(Γ) 元组（`hcapWL hcenE hfootE hrerunE8` 留作 eta 参数）。 -/
example (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{0}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {qc : CutoffParameters} {kk : ℕ} {Ctime Ctime₁ : ℝ≥0}
    (hP5L : LateLinkedRecordsSupply_C11E F qc) (hδq : Tendsto qc.delta atTop (𝓝 0)) : True := by
  have hS := smallDeltaLateRecords_bad_P6HD.{0} Γ hP5L hδq
  have _hbd := ObservedHistory.hbd_stage_late_smallDelta_CXHB2 (F := F) (Ctime := Ctime)
    (Ctime₁ := Ctime₁) (kk := kk) (ε := Γ.epsilon) (C1 := C1P6_C11GT6.{0} p6X1std_C11GT6.{0} Γ)
    (C2 := C2P6_C11GT6.{0} p6X2std_C11GT6.{0} Γ)
    (C1f := max (p6BadC_C11G2.{0} Γ) 9 + Real.sqrt (p6BadC_C11G2.{0} Γ))
    (C2f := 1200 * p6BadC_C11G2.{0} Γ) (m := htransMBad_C11G7B.{0} Γ)
    (η₁ := p6FineEta_C11GT6 Γ.epsilon) (C1₁ := p6BadC_C11G2.{0} Γ) (C2₁ := p6BadC_C11G2.{0} Γ)
    (hSD := hS.1) (heps := hS.2.1) (hδ := hS.2.2) (hε := Γ.epsilon_pos)
    (hη₁ := p6FineEta_pos_C11GT6 Γ.epsilon_pos) (hη := thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon)
    (hsmall := fineEta_le_bJS_C11CL3 Γ.epsilon) (hC1₁ := one_le_p6BadC_C11G7B.{0} Γ)
    (hC2₁ := one_le_p6BadC_C11G7B.{0} Γ) (hC1f := le_rfl) (hC2f := le_rfl)
    (hm := min_le_left _ _) (hm' := min_le_right _ _) (h1 := (hdomL_bad_C11G7B.{0} Γ).1)
    (h2 := by linarith [(hdomL_bad_C11G7B.{0} Γ).2])
  trivial

end GC.LongTime.Ch11
