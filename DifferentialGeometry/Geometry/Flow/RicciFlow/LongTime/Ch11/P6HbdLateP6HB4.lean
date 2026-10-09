import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB3

/-!
# hbd 的 (S) 支 rev4：`htrans` 收窄为 selected-family eventual 形 `htransE`（O-CH11-SFPFIX3，`_P6HB4`）

R-C11-13 D-7（Q4 "htrans 是否也应收窄为 eventual"，接受）：`htrans` 分两层——单 event 层保留局部条件定理
（`htrans_event_CXHT`：record、δ-smallness、footprint、四型 transfer，不动）；tower 消费层改用 selected-family
**`htransE`**：
`∀ᶠ k, ∀ p' q, HEq (y k) q → RegularCrossing p' q → ∀ D, ¬ W_out(q) → ∃ᶠ n, ¬ W_fine(v_n, p')`
（外层 eventually 的尾可依赖 family；内层 frequently 不要求统一的 `n`-尾）。与 `hfootE` 同模式：前提 = `hcenE` /
`hfootE` 的全部序列前提 + 显式 `i k`（`hfootE.txt` 前 37 行逐字，`^ (2 : ℕ)` 拼写，elaborated term 与 `^ 2`
相同）；文本 `build-logs/scratch/O-CH11-SFPFIX3/htransE.txt`。
* **`stage_localizedBad_trans_P6HB4`**（G1，PROVED 相对 binder）：下层取当点 `htransK`
  （加 `HEq y q` 限定）；证明 = rev2 下层证明逐字。
* **`hbd_stage_late_P6HB4`**（G2，PROVISIONAL）：结论 = `hstage` 槽逐字；
  binder `hcapWL hcenE hfootE htransE hrerunE8`，除 `htransE` 外与 `hbd_stage_late_P6HB3` 逐字相同。
* **`htransE_of_htrans_P6HB4`**（G5 桥，PROVED）：旧 `htrans` ⇒ `htransE`（rev4 不强于 rev3）。
陈述由 build-logs/scratch/O-CH11-SFPFIX3/gen_late4.py 从 `P6HbdLateP6HB3.lean` /
`P6HbdLateP6HB2.lean` 源文本生成（逐字抽取 + 定点替换）。
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

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **(S) 的局部化（单 history，transfer 版，当点 `hfootK` + 当点 `htransK`）**：rev4 的下层。陈述同
`stage_localizedBad_trans_P6HB3`，只把 transfer binder 写成**当点**形 `htransK`：对本 history 的实际 crossing 对
`(p', q)` 加 **`HEq y q`** 限定（R-C11-13 D-7：局部化 helper 同步加实际目标限定），其余文本逐字；binder 次序
`hcenK hfootK htransK`（与高层 `hcenE hfootE htransE` 对应）。高层 `hbd_stage_late_P6HB4` 由 `htransE` 的
`∀ᶠ k` 分量逐 `k` 供给。证明 = rev2 下层 `stage_localizedBad_trans_P6HB2` 的证明逐字（该证明对 `htrans` 只在
`q := cast y`、`hq : HEq y q` 的 crossing 上调用一次，故当点形足够；无新数学）。 -/
theorem stage_localizedBad_trans_P6HB4 (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime : ℝ≥0}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2
        ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier)
    (hσ : (σ : ℝ) = H.time i.succ) (haσ : aSeed < σ) {L : ℝ}
    (hcenK : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
        (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t)
            (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / (4 * Real.sqrt (metricScalarAt
              (H.stageMetric (H.activeStage σ) σ) y))))
    (hfootK : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (htransK : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
        W.capTubeHasNeckChart ε) →
      ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
        ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁)
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y) :
    LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
      (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) η₁ C1₁ C2₁
        z, W.capTubeHasNeckChart η₁)
      (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
      (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
        riemannianEDistOf (H.stageMetric (H.activeStage t) t)
          (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1) (H.activeStage_mono h.2)) z
        else 0)
      σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
      (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hsT)) y) := by
  obtain rfl : σ = H.stageTime i.succ := Subtype.ext hσ
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  obtain ⟨q, hq⟩ : ∃ q : (H.stage i.succ).Carrier, HEq y q :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hP) y, (cast_heq _ _).symm⟩
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  rcases Rc.postCover_P6S2 q with ⟨b, x, hbx⟩ | ⟨p', hcross⟩
  · exact (Rc.false_of_stage_cap_P6S2 hcapW b x (hq.trans (heq_of_eq hbx)) hsel).elim
  obtain ⟨D⟩ := hfootK p' q hq hcross
  have hnot : ¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
      W.capTubeHasNeckChart ε := fun hW =>
    hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
      (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
        ((ObservedHistory.spatial_iff_heq_P6S2 hP hg hq).mpr hW))
  have hfreq := htransK p' q hq hcross D hnot
  have hRy := scalar_heq_P6ST2 hP hg hq
  intro δ hδ η hη
  have hratio : ∀ᶠ n in atTop, |metricScalarAt ((H.event i).incoming.flow.base.metric (D.v n)) p' /
      metricScalarAt (H.event i).outputMetric q - 1| < η := by
    filter_upwards [Metric.tendsto_nhds.mp D.ratio_tendsto_one η hη] with n hn
    rwa [Real.dist_eq] at hn
  have hD := hcenK p' q hq hcross D
  have haσ' : (aSeed : ℝ) < H.time i.succ := haσ
  have hlow : ∀ᶠ n in atTop, (aSeed : ℝ) < D.v n := D.v_tendsto.eventually (lt_mem_nhds haσ')
  obtain ⟨n, hbad, hn1, hn2, hn3, hn4⟩ := (hfreq.and_eventually ((D.v_tendsto.eventually
    (lt_mem_nhds (sub_lt_self (H.time i.succ) hδ))).and (hratio.and (hD.and hlow)))).exists
  have hIcc := H.mem_Icc_of_mem_slab_P6ST2 i (D.v_mem n)
  let t : Icc (0 : ℝ) H.horizon := ⟨D.v n, hIcc⟩
  have ht0 : H.time i.castSucc ≤ t := (D.v_mem n).1.le
  have ht1 : (t : ℝ) < H.time i.succ := (D.v_mem n).2
  have hPt : H.stageAt t = H.stage i.castSucc :=
    congrArg H.stage (H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1)
  obtain ⟨z, hz⟩ : ∃ z : (H.stageAt t).Carrier, HEq z p' :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hPt).symm p', cast_heq _ _⟩
  have hsc := scalar_heq_P6ST2 hPt (ObservedHistory.stageMetric_slab_heq_P6ST2 i ht0 ht1) hz
  have hav : aSeed ≤ t := Subtype.coe_le_coe.mp hn4.le
  have hσT : H.time i.succ ≤ (Tn : ℝ) := Subtype.coe_le_coe.mpr hsT
  have hvt : t ≤ Tn := Subtype.coe_le_coe.mp (ht1.le.trans hσT)
  refine ⟨t, z, hn1, ht1, fun hW => hbad ((ObservedHistory.spatial_iff_heq_P6S2 hPt
    (ObservedHistory.stageMetric_slab_heq_P6ST2 i ht0 ht1) hz).mp hW), ?_, ?_⟩
  · change |metricScalarAt (H.stageMetric (H.activeStage t) t) z / _ - 1| < η
    rw [hsc, hRy]
    exact hn2
  · change (if h : aSeed ≤ t ∧ t ≤ Tn then _ else 0) ≤ _
    split_ifs with hh
    · exact hn3 t z rfl hz hav hvt
    · exact absurd ⟨hav, hvt⟩ hh

end GeometricCutoffRecord

namespace ObservedHistory

/-- **(S) 支（`hstage` 槽），rev4：`htrans` → `htransE`**：结论 = `hstage` 槽逐字（同 `hbd_stage_late_P6HB3`）；
binder `hcapWL hcenE hfootE htransE hrerunE8`（五个），`hcapWL hcenE hfootE hrerunE8` 与 rev3 逐字相同。
**`htransE`**（R-C11-13 D-7，`build-logs/scratch/O-CH11-SFPFIX3/htransE.txt` 逐字）= `hfootE` 的全部序列前提 +
显式 `i k` ⇒ `∀ᶠ k`，对实际 crossing 对 `(p', q)`（`HEq (y k) q`）与 footprint 数据 `D`，目标层 `¬ W_out(q)` ⇒
`∃ᶠ n, ¬ W_fine(v_n, p')`（外层 eventually 的尾依赖 family；内层 frequently 无统一 `n`-尾）。证明照 rev3：
`htransE` 的 `∀ᶠ k` 与 `hcapWL`、`hcenE`、`hfootE` 同进 `filter_upwards`，尾部由
`rerun_data_of_localized_ev_P6HB` 吸收；逐 `k` 交下层 `stage_localizedBad_trans_P6HB4`（当点 `htransK`）。 -/
theorem hbd_stage_late_P6HB4 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (htransE :
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
            W.capTubeHasNeckChart η₁)
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
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii hS
  choose i hi using hS
  have hlate : Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_)
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        two_pos)
    have hck := hc k
    have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have hcl := hclock k
    have h1k := h1 k
    have hT := hTc k
    rw [← hi k]
    nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
      mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]
  have hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
        (fun t z => ¬ ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric ((Kh k).activeStage t) t)
          η₁ C1₁ C2₁ z, W.capTubeHasNeckChart η₁)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k)) := by
    filter_upwards [hcapWL ind c hc i hlate, hcenE ind c hc Tn pT hTc aSeed haT hclock h1 hsm
      seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi,
      hfootE ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
      hL hsel hgood hwin hwin' hroom hradii i hi,
      htransE ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
      hL hsel hgood hwin hwin' hroom hradii i hi]
      with k hW hE hF hT
    intro hak _
    choose pp Rc hW using hW
    rw [hRdef k] at hE ⊢
    exact Rc.stage_localizedBad_trans_P6HB4 hW (haT k) (seedTrace k) (hsT k) (has k) (y k)
      (hi k) hak hE hF hT (hsel k)
  have hlo : ∀ k, (Kh k).time (i k).castSucc < σ k := fun k => by
    rw [hi k]
    exact (Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))
  have hdat := rerun_data_of_localized_ev_P6HB (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    Tn aSeed haT pT seedTrace σ y R L hsT has hRpos hRr hL hgood hwin hwin' hroom
    (fun k => (Kh k).time (i k).castSucc) hlo hloc
  choose φ hφ hφk t z R' hsT' has' hR'def hlt hbad hR'pos hR'r hgood' hwin2 hwin3 hroom' hradii'
    using hdat
  have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k => by
    have h := hTc (φ k)
    have hk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk k
    linarith
  exact hrerunE8 (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k))
    (fun k => Tn (φ k)) (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
    (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k)) (fun k => seedTrace (φ k))
    t z R' hsT' has' (fun k => L (φ k) / 2) hR'def hR'pos (fun k => (hR'r k).le)
    ((hL.comp hφ.tendsto_atTop).atTop_div_const two_pos)
    (fun k hg => hbad k hg.1)
    hgood' hwin2 hwin3 hroom' hradii'
    (fun k => ⟨i (φ k), (hlt k).1, (hlt k).2.trans_eq (hi (φ k))⟩) hR'r

/-- **桥（G5，PROVED）**：旧 tower 槽 `htrans`（对任意 `nn cc i` 与该 event 的**所有** crossing 量化）⇒ 新槽
`htransE`（selected family 上 `∀ᶠ k`，只对 `HEq (y k) q` 的 crossing）。逐 `k` 实例化旧槽（`ind k, c k, i k`），
丢弃 `HEq` 前提，`∀ᶠ k` 由 `Eventually.of_forall`；即旧 binder 是 `htransE` 的较强充分条件，rev4 不比 rev3 强
（consumer 见审计；CX-HTRANS 的 `htrans_of_transfers_CXHT` 经此桥直接填 `htransE`）。 -/
theorem htransE_of_htrans_P6HB4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ}
    (htrans : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
          W.capTubeHasNeckChart ε) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁) :
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
  intro ind c hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _
  exact Eventually.of_forall fun k p' q _ => htrans (ind k) (c k) (hc k) (i k) p' q

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
