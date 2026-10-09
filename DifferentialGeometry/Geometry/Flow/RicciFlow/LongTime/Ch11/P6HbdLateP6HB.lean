import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LeftShiftCoreP6HB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowWitnessP6CW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestBoundaryP6HR

/-!
# hbd 的 (S) / (H°) 支：transfer 版 + late `hcapW`（O-CH11-HREST2 G3a，后缀 `_P6HB`）

**修正 G1 / G2 的坏点谓词链**（STAB4 14:2x 回报）：G1 / G2 经 fine-margin 坏 ⇒ `¬Good η₁`，需要 binder
`hcw`（cap / whole-component 型 witness ⇒ fine-margin witness）；但 `HasMargins` 第一合取要求 alternative 是
neck / cap，positive / round 型**永远**不能成 fine-margin witness ⇒ `hcw` 的 whole 半不可填。本文件改为在
**目标层直接取 transfer 逆否**：binder **`htrans`**（crossing 对 + footprint 数据 `D` + 目标层无 witness ⇒
frequently `(D.v n, p')` 无 `(η₁, C1₁, C2₁)` spatial witness），坏点谓词即 `¬∃ W η₁`，直接给 `¬Good η₁`。
`htrans` 的 producer 按 witness 类型分拆（neck：STAB4 G1′ neck 改善 + STAB2 G1 transfer；positive：STAB4 G3
`wholeComponent_positive_transfer_P6ST4`；cap：深度余量 BLOCKED；round：BLOCKED），frequently 形需各型
transfer 的 frequently 版 + 类型鸽笼（STAB4 已提议 `eventually_capOrRound_of_target_not`）。
另把 G1 的 `hcapW`（对所有 event）收窄为 **late** `hcapWL`（沿 stage 序列 eventually），并由 HCAPW 归约到
late records：
* `stage_localizedBad_trans_P6HB`：G1a 局部化的 transfer 版（证明照 G1a，换 `htrans`）。
* `rerun_data_of_localized_ev_P6HB`：G1a 序列引理的 eventual 局部化版（尾部 `N` 同时吸收）。
* **`hbd_stage_late_P6HB`**：结论 = `hstage` 槽逐字；binder `hcapWL`、`hfoot`、`htrans`、`hseedFP`、
  `hcen`、`hrerunE8`。lateness `c k · time (i k).succ → ∞` 由前缀证出：
  `c σ ≥ c (Tn − 1) ≥ c·Tn/2 ≥ (k+1)/2`。
* **`hbd_hor_late_P6HB`**：结论 = `hhor` 槽逐字；binder **`hlocH`**（坏点谓词 `¬∃ W η₁`）、`hrerunF8`。
* **`hcapWL_of_records_P6HB`**：HCAPW `hcapW_of_standardClose_P6CW` ⇒ `hcapWL`，剩 late records binder
  （late event eventually 有 `hasCanonicalWindow` 且三参数阈值任意细的 record）。
`hrerunE8` / `hrerunF8` 与 G1 / G2 逐字相同（坏点 `¬Good η₁ C1₁ C2₁ Ctime₁`、阈值 `8 * R k`）。
**rev1**（lead 14:4x / STAB4 G4 核对）：`hcen` 加前件 `RegularCrossing p' q →` 与种子 terminal footprint
（`seedDist_seq_le_P6ST4` 的 `hco / hd0 / hd / hr / hK / hKold` 形，种子点经 `HEq` 对到 seed trace），后者由新
binder **`hseedFP`** 供给——弱化 `hcen`，owner 同 P-F `hL` 家族（STAB3 / STAB4）。
陈述由 build-logs/scratch/O-CH11-HREST2/mk_g3a.py 从 G1a 文本与 HREST G2 binder 文本生成。
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

/-- **(S) 的局部化（单 history，transfer 版）**：见文件头。`hcapW` + `hfoot` + **`htrans`**（目标层
无 witness ⇒ frequently `(D.v n, p')` 无 `η₁` witness）+ `hcen` + `hsel` ⇒ `σ` 左侧 localized 坏点
（Bad = 无 `(η₁, C1₁, C2₁)` spatial witness，曲率比任意接近 1、seed distance 余量 `L/(4√R)`）。 -/
theorem stage_localizedBad_trans_P6HB (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime : ℝ≥0}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2
        ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier)
    (hσ : (σ : ℝ) = H.time i.succ) (haσ : aSeed < σ)
    (hR : 0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) {L : ℝ} (hL : 0 < L)
    (hfoot : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (htrans : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
        W.capTubeHasNeckChart ε) →
      ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
        ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁)
    (hseedFP : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      (∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
      (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
      (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
      H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
      HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
        (H.activeStage_mono hvt)) o) ∧
      HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
      (H.activeStage_mono hsT)) o' ∧
      0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
      ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
      IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
      ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
      Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
      ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
        interior (Subtype.val '' (H.event i).old)))
    (hcen : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      (∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
      (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
      (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
      H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
      HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
        (H.activeStage_mono hvt)) o) ∧
      HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
      (H.activeStage_mono hsT)) o' ∧
      0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
      ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
      IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
      ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
      Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
      ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
        interior (Subtype.val '' (H.event i).old)) →
      ∀ (D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) (η : ℝ), 0 < η →
      ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
        (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t)
            (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal η)
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
  obtain ⟨D⟩ := hfoot p' q hq hcross
  have hnot : ¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
      W.capTubeHasNeckChart ε := fun hW =>
    hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
      (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
        ((ObservedHistory.spatial_iff_heq_P6S2 hP hg hq).mpr hW))
  have hfreq := htrans p' q hcross D hnot
  have hRy := scalar_heq_P6ST2 hP hg hq
  intro δ hδ η hη
  have hratio : ∀ᶠ n in atTop, |metricScalarAt ((H.event i).incoming.flow.base.metric (D.v n)) p' /
      metricScalarAt (H.event i).outputMetric q - 1| < η := by
    filter_upwards [Metric.tendsto_nhds.mp D.ratio_tendsto_one η hη] with n hn
    rwa [Real.dist_eq] at hn
  have hsq : 0 < Real.sqrt (metricScalarAt
      (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) y) :=
    Real.sqrt_pos.mpr hR
  have hD := hcen p' q hq hcross (hseedFP p' q hq hcross) D (L / (4 * Real.sqrt (metricScalarAt
    (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) y))) (by positivity)
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

/-- **重跑数据（eventual 局部化版）**：同 G1a `rerun_data_of_localized_P6HB`，但逐项局部化只要
`∀ᶠ k`（尾部 `N` 同时吸收）。尾部 `N`（`hwin` 取 `T = 1` ⇒ `aSeed < σ`；
`L → ∞` ⇒ `L > 0`）、子列 `φ k = 2(k+N)+2`；CX-STAGE `localized_left_bad_sequence_CXST`（左端
`max aSeed lo`）选坏点 `(t k, z k)`；P6BND2 `leftShift_rerun_P6S2` 给阈值 `8R'` 的新 `hgood`；新窗口条件由
`R(σ−t) → 0`、`R'/R → 1`、`R/2 ≤ R'` 推出。 -/
theorem rerun_data_of_localized_ev_P6HB {Kh : ℕ → ObservedHistory.{u}} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {Bad : ∀ k (t : Icc (0 : ℝ) (Kh k).horizon), ((Kh k).stageAt t).Carrier → Prop}
    (Tn aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k)
    (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
    (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
      ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
    (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
    (R L : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k)
    (hRpos : ∀ k, 0 < R k) (hRr : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k) (hL : Tendsto L atTop atTop)
    (hgood : ∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
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
        (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k)
    (hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k)
    (hroom : Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop)
    (lo : ℕ → ℝ) (hlo : ∀ k, lo k < σ k)
    (hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ)) (Bad k)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, k ≤ φ k) ∧
    ∃ (t : ∀ k, Icc (0 : ℝ) (Kh (φ k)).horizon) (z : ∀ k, ((Kh (φ k)).stageAt (t k)).Carrier)
      (R' : ℕ → ℝ) (hsT' : ∀ k, t k ≤ Tn (φ k)) (has' : ∀ k, aSeed (φ k) ≤ t k),
      (∀ k, R' k =
        metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k)) (z k)) ∧
      (∀ k, lo (φ k) < t k ∧ (t k : ℝ) < σ (φ k)) ∧
      (∀ k, Bad (φ k) (t k) (z k)) ∧
      (∀ k, 0 < R' k) ∧ (∀ k : ℕ, (k : ℝ) + 1 < R' k) ∧
      (∀ k, ∀ (v : Icc (0 : ℝ) (Kh (φ k)).horizon) (hav : aSeed (φ k) ≤ v) (hvs : v ≤ t k),
        (t k : ℝ) - (L (φ k) / 2) ^ 2 / R' k ≤ (v : ℝ) →
        ∀ w : ((Kh (φ k)).stageAt v).Carrier,
          riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage v) v)
              ((seedTrace (φ k)).point ((Kh (φ k)).activeStage v)
                ((Kh (φ k)).activeStage_mono hav)
                ((Kh (φ k)).activeStage_mono (hvs.trans (hsT' k)))) w ≤
            riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k))
                ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (t k))
                  ((Kh (φ k)).activeStage_mono (has' k))
                  ((Kh (φ k)).activeStage_mono (hsT' k))) (z k) +
              ENNReal.ofReal (L (φ k) / 2 / Real.sqrt (R' k)) →
          8 * R' k ≤ metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage v) v) w →
          (Kh (φ k)).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v w) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed (φ k) : ℝ) ≤ t k - T / R' k) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop,
        (Tn (φ k) : ℝ) - 1 ^ 2 / 2 ≤ (t k : ℝ) - T / R' k) ∧
      Tendsto (fun k => R' k * ((t k : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun k => 1 / 200 * Real.sqrt (R' k)) atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((hwin 1 one_pos).and (hL.eventually_gt_atTop 0)).and hloc)
  let φ : ℕ → ℕ := fun k => 2 * (k + N) + 2
  have hφmono : StrictMono φ := fun a b hab => by
    change 2 * (a + N) + 2 < 2 * (b + N) + 2
    omega
  have hφk : ∀ k, k ≤ φ k := fun k => by
    change k ≤ 2 * (k + N) + 2
    omega
  have hφN : ∀ k, N ≤ φ k := fun k => by
    change N ≤ 2 * (k + N) + 2
    omega
  have hφt : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have haσ : ∀ k, aSeed (φ k) < σ (φ k) := fun k => by
    have h := (hN (φ k) (hφN k)).1.1
    have hr := hRpos (φ k)
    have : 0 < 1 / R (φ k) := by positivity
    exact Subtype.coe_lt_coe.mp (by linarith)
  have hLpos : ∀ k, 0 < L (φ k) := fun k => (hN (φ k) (hφN k)).1.2
  have ha : ∀ k, max (aSeed (φ k) : ℝ) (lo (φ k)) < σ (φ k) := fun k =>
    max_lt (Subtype.coe_lt_coe.mpr (haσ k)) (hlo (φ k))
  obtain ⟨t, z, hfact, hA, hρ⟩ := localized_left_bad_sequence_CXST
    (a := fun k => max (aSeed (φ k) : ℝ) (lo (φ k)))
    (fun k => (hN (φ k) (hφN k)).2 (haσ k) (hLpos k)) ha (fun k => hRpos (φ k)) hLpos
  have has' : ∀ k, aSeed (φ k) ≤ t k := fun k =>
    Subtype.coe_le_coe.mp ((le_max_left _ _).trans (hfact k).1.le)
  have hsT' : ∀ k, t k ≤ Tn (φ k) := fun k =>
    Subtype.coe_le_coe.mp ((hfact k).2.1.le.trans (Subtype.coe_le_coe.mpr (hsT (φ k))))
  let R' : ℕ → ℝ := fun k =>
    metricScalarAt ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k)) (z k)
  have hhalf : ∀ k, R (φ k) / 2 ≤ R' k := fun k => (hfact k).2.2.2.1
  have hR'pos : ∀ k, 0 < R' k := fun k => by
    have := hRpos (φ k)
    have := hhalf k
    linarith
  have hR'r : ∀ k : ℕ, (k : ℝ) + 1 < R' k := fun k => by
    have hcast : ((φ k : ℕ) : ℝ) = 2 * ((k : ℝ) + N) + 2 := by
      change ((2 * (k + N) + 2 : ℕ) : ℝ) = _
      push_cast
      ring
    have := hRr (φ k)
    have := hhalf k
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  refine ⟨φ, hφmono, hφk, t, z, R', hsT', has', fun _ => rfl,
    fun k => ⟨(le_max_right _ _).trans_lt (hfact k).1, (hfact k).2.1⟩,
    fun k => (hfact k).2.2.1, hR'pos, hR'r, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hσσ : t k ≤ σ (φ k) := Subtype.coe_le_coe.mp (hfact k).2.1.le
    have hc := (hfact k).2.2.2.2.2
    have hcen : riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (t k)) (t k))
        ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (t k))
          ((Kh (φ k)).activeStage_mono (has' k))
          ((Kh (φ k)).activeStage_mono (hσσ.trans (hsT (φ k))))) (z k) ≤
        riemannianEDistOf ((Kh (φ k)).stageMetric ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k)))
            ((seedTrace (φ k)).point ((Kh (φ k)).activeStage (σ (φ k)))
              ((Kh (φ k)).activeStage_mono (has (φ k)))
              ((Kh (φ k)).activeStage_mono (hsT (φ k)))) (y (φ k)) +
          ENNReal.ofReal (L (φ k) / (4 * Real.sqrt (R (φ k)))) := by
      split_ifs at hc with hh
      · exact hc
      · exact absurd ⟨has' k, hsT' k⟩ hh
    exact leftShift_rerun_P6S2 (haT (φ k)) (hsT (φ k)) (has (φ k)) hσσ (has' k)
      (seedTrace (φ k)) (y (φ k)) (z k) (hRpos (φ k)) (hhalf k) (hLpos k).le
      (hfact k).2.2.2.2.1 hcen (hgood (φ k))
  · intro T hT
    filter_upwards [hφt.eventually (hwin (3 * T) (by positivity)), hA.eventually (gt_mem_nhds hT)]
      with k hk1 hk2
    have hr := hRpos (φ k)
    have hr' := hR'pos k
    have e1 : (σ (φ k) : ℝ) - t k < T / R (φ k) := by
      rw [lt_div_iff₀ hr]
      linarith
    have e2 : T / R' k ≤ 2 * T / R (φ k) := by
      rw [div_le_div_iff₀ hr' hr]
      nlinarith [hhalf k]
    have e3 : 3 * T / R (φ k) = T / R (φ k) + 2 * T / R (φ k) := by ring
    linarith
  · intro T hT
    filter_upwards [hφt.eventually (hwin' (3 * T) (by positivity)), hA.eventually (gt_mem_nhds hT)]
      with k hk1 hk2
    have hr := hRpos (φ k)
    have hr' := hR'pos k
    have e1 : (σ (φ k) : ℝ) - t k < T / R (φ k) := by
      rw [lt_div_iff₀ hr]
      linarith
    have e2 : T / R' k ≤ 2 * T / R (φ k) := by
      rw [div_le_div_iff₀ hr' hr]
      nlinarith [hhalf k]
    have e3 : 3 * T / R (φ k) = T / R (φ k) + 2 * T / R (φ k) := by ring
    linarith
  · have hB := hroom.comp hφt
    have hlow := tendsto_atTop_add_const_right atTop (-2) (hB.atTop_div_const two_pos)
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [hB.eventually_gt_atTop 0, hA.eventually (gt_mem_nhds one_pos),
      hρ.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with k hk1 hk2 hk3
    have hr := hRpos (φ k)
    simp only [comp_apply] at hk1 ⊢
    have hX : 0 ≤ (σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2) :=
      (pos_of_mul_pos_right hk1 hr.le).le
    have hst : 0 ≤ (σ (φ k) : ℝ) - t k := sub_nonneg.mpr (hfact k).2.1.le
    have hR'2 : R' k ≤ 2 * R (φ k) := by
      rw [div_lt_iff₀ hr] at hk3
      linarith
    have i1 := mul_le_mul_of_nonneg_right (hhalf k) hX
    have i2 := mul_le_mul_of_nonneg_right hR'2 hst
    have e1 : R' k * ((t k : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) =
        R' k * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) - R' k * ((σ (φ k) : ℝ) - t k) := by
      ring
    have e2 : R (φ k) * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) / 2 =
        R (φ k) / 2 * ((σ (φ k) : ℝ) - ((Tn (φ k) : ℝ) - 1 ^ 2 / 2)) := by ring
    have e3 : 2 * R (φ k) * ((σ (φ k) : ℝ) - t k) = 2 * (R (φ k) * ((σ (φ k) : ℝ) - t k)) := by
      ring
    linarith
  · have hR'top : Tendsto R' atTop atTop := tendsto_atTop_mono (fun k => (hR'r k).le)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    exact Tendsto.const_mul_atTop (by norm_num) (Real.tendsto_sqrt_atTop.comp hR'top)

/-- **(S) 支（`hstage` 槽），transfer + late `hcapWL` 版**：见文件头。 -/
theorem hbd_stage_late_P6HB {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hfoot : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (htrans : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 q,
          W.capTubeHasNeckChart ε) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p', W.capTubeHasNeckChart η₁)
    (hseedFP : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier), (σ : ℝ) = H.time i.succ →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
        (H.event i).RegularCrossing p' q →
        (∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
          (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
          (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
            H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
            HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) o) ∧
          HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) o' ∧
          0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
            ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
          IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
          Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
              interior (Subtype.val '' (H.event i).old)))
    (hcen : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier), (σ : ℝ) = H.time i.succ →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
        (H.event i).RegularCrossing p' q →
        (∃ (o : (H.stage i.castSucc).Carrier) (o' : (H.stage i.succ).Carrier)
          (hco : (H.event i).RegularCrossing o o') (r d : ℝ),
          (∀ (t : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ t) (hvt : t ≤ Tn),
            H.time i.castSucc ≤ t → (t : ℝ) < H.time i.succ →
            HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) o) ∧
          HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) o' ∧
          0 ≤ d ∧ riemannianEDistOf (I := ThreeModel) (H.event i).outputMetric o' q =
            ENNReal.ofReal d ∧ 17 * (d + 1) < 16 * r ∧
          IsCompact (riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r) ∧
          Subtype.val '' riemannianClosedBallOf (I := ThreeModel) (H.event i).terminal.metric
            ⟨o, hco.mem_terminalRegularRegion (H.event i)⟩ r ⊆
              interior (Subtype.val '' (H.event i).old)) →
        ∀ (D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) (η : ℝ), 0 < η →
        ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
          (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
          riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) z ≤
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hsT)) y +
              ENNReal.ofReal η)
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
    filter_upwards [hcapWL ind c hc i hlate] with k hW
    intro hak hLk
    choose pp Rc hW using hW
    rw [hRdef k]
    exact Rc.stage_localizedBad_trans_P6HB hW (haT k) (seedTrace k) (hsT k) (has k) (y k)
      (hi k) hak (hRdef k ▸ hRpos k) hLk
      (hfoot (ind k) (c k) (hc k) (i k) (σ k) (y k) (hi k) (hsel k))
      (htrans (ind k) (c k) (hc k) (i k))
      (hseedFP (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (i k) (σ k)
        (hsT k) (has k) (y k) (hi k) (hsel k))
      (hcen (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (i k) (σ k)
        (hsT k) (has k) (y k) (hi k) (hsel k))
      (hsel k)
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

/-- **(H°) 支（`hhor` 槽），transfer 版**：见文件头。`hlocH` 直接给 `¬∃ W η₁` 的 localized 坏点。 -/
theorem hbd_hor_late_P6HB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    (hlocH : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            η₁ C1₁ C2₁ z, W.capTubeHasNeckChart η₁)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y))
    (hrerunF8 :
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
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False) :
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
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
          (σ k : ℝ) = (Kh k).horizon) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii hH
  have hloc : ∀ k, aSeed k < σ k → 0 < L k →
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
    intro k hak hLk
    rw [hRdef k]
    exact hlocH (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (σ k) (hsT k)
      (has k) (y k) (hH k).1 (hH k).2 hak (hRdef k ▸ hRpos k) (hsel k) (L k) hLk
  have hlo : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < σ k := fun k => by
    rw [(hH k).2]
    exact (hH k).1
  have hdat := rerun_data_of_localized_P6HB (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    Tn aSeed haT pT seedTrace σ y R L hsT has hRpos hRr hL hgood hwin hwin' hroom
    (fun k => (Kh k).time (Fin.last (Kh k).eventCount)) hlo hloc
  choose φ hφ hφk t z R' hsT' has' hR'def hlt hbad hR'pos hR'r hgood' hwin2 hwin3 hroom' hradii'
    using hdat
  have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k => by
    have h := hTc (φ k)
    have hk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk k
    linarith
  exact hrerunF8 (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k))
    (fun k => Tn (φ k)) (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
    (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k)) (fun k => seedTrace (φ k))
    t z R' hsT' has' (fun k => L (φ k) / 2) hR'def hR'pos (fun k => (hR'r k).le)
    ((hL.comp hφ.tendsto_atTop).atTop_div_const two_pos)
    (fun k hg => hbad k hg.1)
    hgood' hwin2 hwin3 hroom' hradii'
    (fun k => ⟨(hlt k).1, (hlt k).2.trans_eq (hH (φ k)).2⟩)

/-- **HCAPW ⇒ `hcapWL`**：`hcapW_of_standardClose_P6CW` 的常数 `Cs`（只依赖 `ε`）先取；`C1, C2 ≥ Cs`
时，late records binder（late event eventually 有 `hasCanonicalWindow` 且参数任意细的 record）给出
`hbd_stage_late_P6HB` 的 `hcapWL` 槽逐字。 -/
theorem hcapWL_of_records_P6HB {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
    (∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder) →
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)),
              W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, Rcap, mcap, εcap, hCs, hεcap, hW⟩ :=
    GeometricCutoffRecord.hcapW_of_standardClose_P6CW.{u} hε hε'
  refine ⟨Cs, hCs, fun C1 C2 h1 h2 hrec => ?_⟩
  intro ind c hc Kh i hlate
  filter_upwards [hrec ind c hc i hlate εcap Rcap mcap hεcap] with k hk
  obtain ⟨pp, Rc, hcan, hacc, hrad, hord⟩ := hk
  exact ⟨pp, Rc, hW Rc hcan hacc hrad hord C1 C2 h1 h2⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
