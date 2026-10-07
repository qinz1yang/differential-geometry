import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalizedTransferP6ST2

/-!
# hbd 左移路线的核心（O-CH11-HREST2 G1a，后缀 `_P6HB`）

HREST G3 `canonicalLateCore_of_normalizedS_hclos4_P6HR` 的 `hbd` 槽（(S) `σ k = time (i k).succ` ∨
(H°) `time last < horizon = σ k`）走左移路线。本文件给两条与 tower 无关的核心引理：

* **`stage_localizedBad_P6HB`**（单 history，(S) 的局部化）：stage 时刻 `σ = time i.succ` 的 post 点 `y`
  （`hsel : ¬ Good ε C1 C2 Ctime`），post-cover 二分：cap-model 支由 **`hcapW`** 收口
  （`false_of_stage_cap_P6S2`）；crossing 支取 **`hfoot`** 的 `BufferedFootprintData_P6ST2` `D`，
  STAB2 G1 transfer 的逆否（`frequently_not_fineMargin_P6ST2`）给 frequently fine-margin 坏
  `(D.v n, p')`；曲率比 `→ 1` 来自
  `D.ratio_tendsto_one`；seed distance 来自 **`hcen`**（种子中心位移：任意 `η > 0`，eventually
  `d_{D.v n}(seed, p') ≤ d_σ(seed, y) + η`）。结论是 CX-STAGE 的 `LeftLocalizedBadAt_CXST`，seed distance
  用 `dite` 取 seed trace 的逐时刻点（区间 `[aSeed, Tn]` 外取 `0`；stage 可空，不能取任意默认点，
  故不直接调用 `stage_class_localizedBad_P6ST2`，证明照其改写）。
* **`rerun_data_of_localized_P6HB`**（序列层，对坏点谓词 `Bad` 与左端 `lo` 泛型，(S)/(H°) 共用）：selection
  数据（`hbd` 前缀：`hgood` 阈值 `4R`、`hwin hwin' hroom hradii`）+ 逐项局部化坏点 ⇒ 子列
  `φ k = 2(k+N)+2` 上的**重跑数据**：`lo < t < σ`、`Bad`、`R' := scalar(t, z)`、`k+1 < R'`、新 `hgood`
  （窗口 `L/2`、**阈值 `8R'`**，P6BND2 `leftShift_rerun_P6S2`）、新 `hwin hwin' hroom hradii`
  （由 CX-STAGE `localized_left_bad_sequence_CXST` 的 `R(σ−t) → 0`、`R'/R → 1` 推出）。
无新 def / structure / 具名 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **(S) 的局部化（单 history）**：见文件头。`hcapW`（S-a）+ `hfoot`（footprint 合同）+ `hcen`（种子中心
位移）+ `hsel` ⇒ `σ` 左侧的 localized fine-margin 坏点（曲率比任意接近 1、seed distance 余量
`L/(4√R)`）。 -/
theorem stage_localizedBad_P6HB (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 ηfine C1f C2f m : ℝ} {kk : ℕ} {Ctime : ℝ≥0}
    (h1 : 2 * C1f ≤ C1) (h2 : 1000 * C2f ≤ C2) (hle : ηfine ≤ neckModelTolerance (ε / 2))
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
    (hcen : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
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
      (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ηfine C1f C2f
        z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
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
  have hfreq := MetricCutCapEvent.frequently_not_fineMargin_P6ST2 D hle h1 h2 hnot
  have hRy := scalar_heq_P6ST2 hP hg hq
  intro δ hδ η hη
  have hratio : ∀ᶠ n in atTop, |metricScalarAt ((H.event i).incoming.flow.base.metric (D.v n)) p' /
      metricScalarAt (H.event i).outputMetric q - 1| < η := by
    filter_upwards [Metric.tendsto_nhds.mp D.ratio_tendsto_one η hη] with n hn
    rwa [Real.dist_eq] at hn
  have hsq : 0 < Real.sqrt (metricScalarAt
      (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) y) :=
    Real.sqrt_pos.mpr hR
  have hD := hcen p' q hq D (L / (4 * Real.sqrt (metricScalarAt
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
  refine ⟨t, z, hn1, ht1, fun hW => hbad ((ObservedHistory.fineMargin_slab_iff_P6ST2 i ht0 ht1
    hz).mp hW), ?_, ?_⟩
  · change |metricScalarAt (H.stageMetric (H.activeStage t) t) z / _ - 1| < η
    rw [hsc, hRy]
    exact hn2
  · change (if h : aSeed ≤ t ∧ t ≤ Tn then _ else 0) ≤ _
    split_ifs with hh
    · exact hn3 t z rfl hz hav hvt
    · exact absurd ⟨hav, hvt⟩ hh

end GeometricCutoffRecord

namespace ObservedHistory

/-- **重跑数据（序列层，对 `Bad` / `lo` 泛型）**：见文件头。尾部 `N`（`hwin` 取 `T = 1` ⇒ `aSeed < σ`；
`L → ∞` ⇒ `L > 0`）、子列 `φ k = 2(k+N)+2`；CX-STAGE `localized_left_bad_sequence_CXST`（左端
`max aSeed lo`）选坏点 `(t k, z k)`；P6BND2 `leftShift_rerun_P6S2` 给阈值 `8R'` 的新 `hgood`；新窗口条件由
`R(σ−t) → 0`、`R'/R → 1`、`R/2 ≤ R'` 推出。 -/
theorem rerun_data_of_localized_P6HB {Kh : ℕ → ObservedHistory.{u}} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
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
    (hloc : ∀ k, aSeed k < σ k → 0 < L k →
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
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hwin 1 one_pos).and (hL.eventually_gt_atTop 0))
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
    have h := (hN (φ k) (hφN k)).1
    have hr := hRpos (φ k)
    have : 0 < 1 / R (φ k) := by positivity
    exact Subtype.coe_lt_coe.mp (by linarith)
  have hLpos : ∀ k, 0 < L (φ k) := fun k => (hN (φ k) (hφN k)).2
  have ha : ∀ k, max (aSeed (φ k) : ℝ) (lo (φ k)) < σ (φ k) := fun k =>
    max_lt (Subtype.coe_lt_coe.mpr (haσ k)) (hlo (φ k))
  obtain ⟨t, z, hfact, hA, hρ⟩ := localized_left_bad_sequence_CXST
    (a := fun k => max (aSeed (φ k) : ℝ) (lo (φ k)))
    (fun k => hloc (φ k) (haσ k) (hLpos k)) ha (fun k => hRpos (φ k)) hLpos
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

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
