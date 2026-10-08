import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenCollarP6HE
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenHistoryP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G

/-!
# `hcenE` 的 producer：`surgery_no_shortcut_C11D` + collar 扩展 hcapW（O-CH11-HCENP G2/G3，后缀 `_P6HE`）

`P6HbdLateP6HB2.hbd_stage_late_P6HB2` 的窄 binder `hcenE`（build-logs/scratch/O-CH11-SFPFIX/
hcenE.txt）不经种子 terminal footprint / hBCD：DIST G3 `surgery_no_shortcut_C11D` 只要两个端点
（种子 `o′` 与坏点 `q`）在 `e⁺` 处不在 cap window 内区 `‖x‖ ≤ transitionEnd + 10`。

* **坏点保护** `bad_not_mem_innerWindow_P6HE`：`hsel`（`¬ HasSpatialCanonicalTimeControl`）+ collar
  扩展 hcapW（`capCollar_of_record_P6HE`，`P6HcenCollarP6HE`）⇒ `q` 不在内区。
* **种子保护** `exists_seed_not_mem_innerWindow_P6HE`：种子标量 `≤ 3`
  （`seed_scalar_le_of_smallParabolic_C11G`，`r = 1`）+ 窗口内区标量 `≥ scale/2`
  （`exists_capWindow_scalar_lower_C11G`）+ `6 < scale`。
* **单 history kernel** `hcenE_history_P6HE`：种子 crossing（`BackwardPointTrace.crossing`，
  `aSeed < σ ≤ Tn`）+ `surgery_no_shortcut_C11D`（`δ` 任意 `> 0`）+ slab HEq 管线
  （照 `hcen_history_P6ST4`）。
* **`hcenE_of_noShortcut_P6HE`（G2 主定理）**：结论 = `hcenE` binder 逐字（`^ (2 : ℕ)` 拼写同
  SFPFIX）。显式 binder：`hCs1 hCs2 : capCollarCs_P6HE ε ≤ C1, C2`（collar 常数与 `p6CapCs` 是
  不同 `Classical.choose`，不可由 CL2 付掉；G3 给 ceiling v2 项）；`hrec`（late-records binder =
  `hcapWL_of_records_P6HB` 的 `hrec` 加第 5 合取项 `∀ b, 6 < scale`；lead 17:2x 裁定不改 P6HB 的
  `hrec`，此处自带）。
* `six_lt_of_nominal_scale_P6HE` / `six_lt_rescaled_scale_P6HE` / `eventually_six_lt_scale_P6HE`：
  KNOM/KDIAG 的 `(n+1)·max(n+1)(Q n) ≤ scale`（`exists_lateKdata_nominal_diag_CXKN` 的
  `S n ≤ scale` 合取项）与 P6WR hOpen 第三合取项（Ho 单位，`scale_K = c · scale_Ho`，
  `rescale_P6M_scale`）蕴含 `6 < scale`（`n ≥ 2`），故第 5 合取对 KNOM witness 免费。
* G3：`p6X1col_P6HE / p6X2col_P6HE`（`p6X1std` 与 collar 常数取 max）与支配引理（ceiling v2 项，
  归 CHAIN/GAPTOP 后继；不改 `p6X1std`）。
* consumer（文件末 `example`）：喂 `hbd_stage_late_P6HB2` 的 `hcenE` 槽。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-! ## 0. 小引理 -/

/-- seed trace 点：stage 指标相等 ⇒ `HEq`。 -/
theorem BackwardPointTrace.point_heq_P6HE {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {endpoint : (H.stage last).Carrier}
    (tr : BackwardPointTrace H first last hle endpoint) {j k : Fin (H.eventCount + 1)} (h : j = k)
    (a : first ≤ j) (b : j ≤ last) (c : first ≤ k) (d : k ≤ last) :
    HEq (tr.point j a b) (tr.point k c d) := by
  subst h
  rfl

/-- NOMID/KDIAG 的 scale 子句 `(n+1)·max(n+1)(Q) ≤ scale`（`n ≥ 2`）⇒ `6 < scale`。 -/
theorem six_lt_of_nominal_scale_P6HE {n : ℕ} (hn : 2 ≤ n) {Q s : ℝ}
    (h : ((n : ℝ) + 1) * max ((n : ℝ) + 1) Q ≤ s) : 6 < s := by
  have hn' : (3 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmax : (3 : ℝ) ≤ max ((n : ℝ) + 1) Q := hn'.trans (le_max_left _ _)
  nlinarith

/-- P6WR `hOpen` 第三合取项（Ho 单位）`(n+1)·max((n+1)/c)(Q) ≤ scale_Ho` ⇒ 重标度后 `6 < c · scale_Ho`
（`rescale_P6M_scale`：`scale_K = c · scale_Ho`）。 -/
theorem six_lt_rescaled_scale_P6HE {n : ℕ} (hn : 2 ≤ n) {c Q s : ℝ} (hc : 0 < c)
    (h : ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c) Q ≤ s) : 6 < c * s := by
  have hn' : (3 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : ((n : ℝ) + 1) * (((n : ℝ) + 1) / c) ≤ s :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)).trans h
  have h2 : ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ c * s := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    calc ((n : ℝ) + 1) * ((n : ℝ) + 1) = c * (((n : ℝ) + 1) * (((n : ℝ) + 1) / c)) := by
          field_simp
      _ ≤ c * s := this
  nlinarith

/-- KNOM/KDIAG 形（逐 `n` 的 scale 下界 `S n ≤ scale`，`S n = (n+1)·max(n+1)(Q n)`）⇒ eventually
`6 < scale`。 -/
theorem eventually_six_lt_scale_P6HE {ι : ℕ → Type*} {sc : ∀ n, ι n → ℝ} {Q : ℕ → ℝ}
    (h : ∀ n (j : ι n), ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤ sc n j) :
    ∀ᶠ n in atTop, ∀ j : ι n, 6 < sc n j := by
  filter_upwards [eventually_ge_atTop 2] with n hn j
  exact six_lt_of_nominal_scale_P6HE hn (h n j)

namespace ObservedHistory

/-- `t < time i.succ` ⇒ `activeStage t ≤ i.castSucc`。 -/
theorem activeStage_le_castSucc_P6HE (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (t : Icc (0 : ℝ) H.horizon) (ht : (t : ℝ) < H.time i.succ) :
    H.activeStage t ≤ i.castSucc := by
  by_contra hlt
  have hsk : i.succ ≤ H.activeStage t := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hlt)
  exact absurd (lt_of_lt_of_le ht ((H.time_strictMono.monotone hsk).trans
    (H.activeStage_time_le t))) (lt_irrefl _)

/-- 种子 trace 在 `e⁺` 的 output 标量 `≤ 3`（K0：`hasSmallParabolicCurvature … 1`，`aSeed = T − 1²`，
`aSeed ≤ σ ≤ T`，`σ = time i.succ`）。 -/
theorem seed_scalar_succ_le_P6HE (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT 1)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - 1 ^ (2 : ℕ))
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (hσ : (σ : ℝ) = H.time i.succ)
    (h1 : H.activeStage aSeed ≤ i.succ) (h2 : i.succ ≤ H.activeStage Tn) :
    metricScalarAt (H.event i).outputMetric (seedTrace.point i.succ h1 h2) ≤ 3 := by
  have h := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace σ has hsT i.succ
    (H.activeStage_eq_succ_of_time_P6ST4 i σ hσ) h1 h2
  rw [hσ, H.stageMetric_succ_time_C11G i] at h
  norm_num at h
  exact h

end ObservedHistory

/-! ## 1. 端点保护 -/

/-- **种子保护（`_P6HE`）**：存在绝对常数 `ε₀ > 0`；record 精度 `≤ ε₀`、阶 `≥ 2`、
`transitionEnd + 10 < modelRadius`、canonical windows、`6 < scale_b`；`e⁺` 处输出标量 `≤ 3` 的点
不在任何 `S_b.window '' {‖x‖ ≤ transitionEnd + 10}`（窗口内区标量 `≥ scale/2 > 3`）。 -/
theorem exists_seed_not_mem_innerWindow_P6HE :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}
        (Rc : GeometricCutoffRecord H i pp), (∀ b, (Rc.static b).hasCanonicalWindow) →
        pp.modelAccuracy ≤ ε₀ → 2 ≤ pp.modelOrder →
        StandardCap.transitionEnd + 10 < pp.modelRadius →
        (∀ b, 6 < (Rc.static b).neck.scale) →
        ∀ {z : (H.stage i.succ).Carrier}, metricScalarAt (H.event i).outputMetric z ≤ 3 →
        ∀ b : (H.event i).RetainedBoundaryIndex, z ∉ (Rc.static b).window ''
          {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_capWindow_scalar_lower_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  rintro H i pp Rc hcan hacc hm hD hscale z hz b ⟨x, hx, rfl⟩
  have hx' : ‖x.val‖ < pp.modelRadius := lt_of_le_of_lt hx hD
  have hlow := h (H.event i) hacc hm (Rc.static b) (hcan b) x hx'
  linarith [hscale b]

namespace ObservedHistory

/-- **坏点保护（`_P6HE`）**：collar 扩展 hcapW（窗口内区点 `‖x‖ ≤ transitionEnd + 10` 处
`SpatialCanonicalWitness ε C1 C2` ∧ `capTubeHasNeckChart ε`）+ `hsel`（`σ = time i.succ` 处
`¬ HasSpatialCanonicalTimeControl`）⇒ 坏点 `q ≍ y` 不在任何内区。 -/
theorem bad_not_mem_innerWindow_P6HE (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {pp : CutoffParameters} (Rc : GeometricCutoffRecord H i pp) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcol : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 ((Rc.static b).window x),
        W.capTubeHasNeckChart ε)
    {σ : Icc (0 : ℝ) H.horizon} (hσ : (σ : ℝ) = H.time i.succ) {y : (H.stageAt σ).Carrier}
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y)
    {q : (H.stage i.succ).Carrier} (hyq : HEq y q) :
    ∀ b : (H.event i).RetainedBoundaryIndex, q ∉ (Rc.static b).window ''
      {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
  rintro b ⟨x, hx, hxq⟩
  obtain ⟨W, hW⟩ := hcol b x hx
  have hσs : H.activeStage σ = i.succ := H.activeStage_eq_succ_of_time_P6ST4 i σ hσ
  have hP : H.stageAt σ = H.stage i.succ := congrArg H.stage hσs
  have hb : H.time (H.activeStage σ) = (σ : ℝ) := by rw [hσs, hσ]
  refine hsel ((hasSpatialCanonicalTimeControl_iff_of_boundary_P6S (Or.inl hb)).mpr
    ((spatial_iff_heq_P6S2 hP (H.stageMetric_heq_output_P6ST4 i σ hσ) hyq).mpr ?_))
  rw [← hxq]
  exact ⟨W, hW⟩

end ObservedHistory

/-! ## 2. 单 history kernel -/

namespace ObservedHistory

/-- **`hcenE` 的单 history kernel（`_P6HE`）**：crossing `p' ↦ q`（`HEq y q`）、种子 trace 跨过 event `i`
（`aSeed < σ = time i.succ ≤ Tn`）、record `Rc`（canonical windows、`modelAccuracy ≤ 1/2`、
`transitionEnd + 10 < modelRadius`）、collar witness（`hcol`）、`hsel`、种子保护（`hseed`）⇒
对任意 `δ > 0` 与 footprint 数据 `D`，eventually 在 `n`：`d_{g(D.v n)}(seed_t, z) ≤ d_{g(σ)}(seed_σ, y) + δ`。
证明 = `surgery_no_shortcut_C11D`（无 footprint、无紧性）+ slab HEq 管线（照 `hcen_history_P6ST4`）。 -/
theorem hcenE_history_P6HE (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {pp : CutoffParameters} (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 C1f C2f m : ℝ} {kk : ℕ} {Ctime : ℝ≥0}
    (hcan : ∀ b, (Rc.static b).hasCanonicalWindow) (hacc : pp.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < pp.modelRadius)
    (hcol : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 ((Rc.static b).window x),
        W.capTubeHasNeckChart ε)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (hσ : (σ : ℝ) = H.time i.succ) (haσ : aSeed < σ)
    (hseed : ∀ (b : (H.event i).RetainedBoundaryIndex) (h1 : H.activeStage aSeed ≤ i.succ)
      (h2 : i.succ ≤ H.activeStage Tn), seedTrace.point i.succ h1 h2 ∉ (Rc.static b).window ''
        {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (y : (H.stageAt σ).Carrier) (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
      ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
        (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t)
            (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y + ENNReal.ofReal δ := by
  intro p' q hyq hcp D
  have haσ' : (aSeed : ℝ) < H.time i.succ := by rw [← hσ]; exact Subtype.coe_lt_coe.mpr haσ
  have hf : H.activeStage aSeed ≤ i.castSucc := H.activeStage_le_castSucc_P6HE i aSeed haσ'
  have hl : i.succ ≤ H.activeStage Tn :=
    H.le_activeStage Tn i.succ (by rw [← hσ]; exact Subtype.coe_le_coe.mpr hsT)
  have hcs : i.castSucc ≤ i.succ := Fin.castSucc_lt_succ.le
  have hco := seedTrace.crossing i hf hl
  have hσs : H.activeStage σ = i.succ := H.activeStage_eq_succ_of_time_P6ST4 i σ hσ
  have hσheq : HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
      (H.activeStage_mono hsT)) (seedTrace.point i.succ (hf.trans hcs) hl) :=
    seedTrace.point_heq_P6HE hσs _ _ _ _
  have hnos := H.surgery_no_shortcut_C11D i (fun b => Rc.static b) Rc.old_eq_retained hcan hacc
    hD hco hcp (hseed · (hf.trans hcs) hl) (H.bad_not_mem_innerWindow_P6HE i Rc hcol hσ hsel hyq)
    hδ
  have hev := (MetricCutCapEvent.tendsto_nhdsLT_of_slab_P6ST3 D.v_mem D.v_tendsto).eventually hnos
  have hRHS : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
      (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y =
      riemannianEDistOf (H.stageMetric i.succ (H.time i.succ))
        (seedTrace.point i.succ (hf.trans hcs) hl) q := by
    rw [H.stageMetric_succ_time_C11G i]
    exact edist_heq_P6ST4 (congrArg H.stage hσs) (H.stageMetric_heq_output_P6ST4 i σ hσ) hσheq hyq
  filter_upwards [hev] with n hn t z ht hz hav hvt
  have ht0 : H.time i.castSucc ≤ t := by
    rw [ht]
    exact (D.v_mem n).1.le
  have ht1 : (t : ℝ) < H.time i.succ := by
    rw [ht]
    exact (D.v_mem n).2
  have hmet : HEq (H.stageMetric (H.activeStage t) t)
      ((H.event i).incoming.flow.base.metric (D.v n)) := by
    have h2 : (H.event i).incoming.flow.base.metric (t : ℝ) =
        (H.event i).incoming.flow.base.metric (D.v n) := by rw [ht]
    exact (stageMetric_slab_heq_P6ST2 i ht0 ht1).trans (heq_of_eq h2)
  have hot : HEq (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
      (H.activeStage_mono hvt)) (seedTrace.point i.castSucc hf (hcs.trans hl)) :=
    seedTrace.point_heq_P6HE (H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1) _ _ _ _
  rw [edist_heq_P6ST4 (congrArg H.stage (H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1)) hmet hot hz,
    hRHS]
  rw [stageMetric_castSucc_apply] at hn
  exact hn

end ObservedHistory

/-! ## 3. 槽：`hcenE` 逐字 -/

/-- **`hcenE` producer（G2 主定理，`_P6HE`）**：结论 = `hbd_stage_late_P6HB2` 的窄 binder `hcenE` **逐字**
（build-logs/scratch/O-CH11-SFPFIX/hcenE.txt，`^ (2 : ℕ)` 拼写同 SFPFIX）。显式 binder：
* `hCs1 hCs2`：`capCollarCs_P6HE ε ≤ C1, C2`（collar 常数 ≠ `p6CapCs`，不可由 CL2 付掉；ceiling v2 项见 G3）；
* `hrec`：late-records binder（`hcapWL_of_records_P6HB` 的 `hrec` 加第 5 合取项 `∀ b, 6 < scale`，
  由 KNOM/KDIAG scale 子句 + `six_lt_of_nominal_scale_P6HE` 免费供给）。
**PROVISIONAL**（binder：`hCs1 hCs2 hrec`）。 -/
theorem hcenE_of_noShortcut_P6HE {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hrec : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale) :
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
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k))) := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi
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
  obtain ⟨ε₀, hε₀, hseedprot⟩ := exists_seed_not_mem_innerWindow_P6HE.{u}
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hRcap, hcolev⟩ :=
    GC.LongTime.Ch11.capCollar_of_record_P6HE.{u} hε hε'
  have hrecEv := hrec ind c hc i hlate (min (min (1 / 2) ε₀) εcap) Rcap (max mcap 2)
    (lt_min (lt_min (by norm_num) hε₀) hεcap)
  have haσ : ∀ᶠ k in atTop, aSeed k < σ k := by
    filter_upwards [hwin 1 one_pos] with k hk
    have h0 : (0 : ℝ) < 1 / R k := by
      have := hRpos k
      positivity
    exact Subtype.coe_lt_coe.mp (by linarith)
  have hLpos : ∀ᶠ k in atTop, 0 < L k := hL.eventually_gt_atTop 0
  filter_upwards [hrecEv, haσ, hLpos] with k hk haσk hLk
  obtain ⟨pp, Rc, hcan, hacc, hrad, hord, hscale⟩ := hk
  have hacc1 : pp.modelAccuracy ≤ 1 / 2 := hacc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hacc2 : pp.modelAccuracy ≤ ε₀ := hacc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hacc3 : pp.modelAccuracy ≤ εcap := hacc.trans (min_le_right _ _)
  have hord1 : mcap ≤ pp.modelOrder := (le_max_left _ _).trans hord
  have hord2 : 2 ≤ pp.modelOrder := (le_max_right _ _).trans hord
  have hD : StandardCap.transitionEnd + 10 < pp.modelRadius := hRcap.trans_le hrad
  have hcol := hcolev Rc hcan hacc3 hrad hord1 C1 C2 hCs1 hCs2
  have hseedk : ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex)
      (h1' : (Kh k).activeStage (aSeed k) ≤ (i k).succ)
      (h2' : (i k).succ ≤ (Kh k).activeStage (Tn k)),
      (seedTrace k).point (i k).succ h1' h2' ∉ (Rc.static b).window ''
        {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} :=
    fun b h1' h2' => hseedprot Rc hcan hacc2 hord2 hD hscale
      ((Kh k).seed_scalar_succ_le_P6HE (i k) (haT k) (hsm k) (hclock k) (seedTrace k) (hsT k)
        (has k) (hi k) h1' h2') b
  have hδ : 0 < L k / (4 * Real.sqrt (R k)) := by
    have := Real.sqrt_pos.mpr (hRpos k)
    positivity
  exact (Kh k).hcenE_history_P6HE (i k) Rc hcan hacc1 hD hcol (haT k) (seedTrace k) (hsT k)
    (has k) (hi k) haσk hseedk (y k) (hsel k) hδ

/-- `hrec`（含 `6 < scale` 第 5 合取项）⇒ `hcapWL_of_records_P6HB` 的 `hrec`（4 合取项）：同一份
late-records 供给同时喂 `hcapWL` 与 `hcenE`。 -/
theorem hrec_of_hrec6_P6HE {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (hrec6 : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder := by
  intro ind c hc Kh i hlate εcap Rcap mcap hεcap
  filter_upwards [hrec6 ind c hc i hlate εcap Rcap mcap hεcap] with k hk
  obtain ⟨pp, Rc, h1, h2, h3, h4, -⟩ := hk
  exact ⟨pp, Rc, h1, h2, h3, h4⟩

/-- **consumer**：`hcenE_of_noShortcut_P6HE` 喂 `hbd_stage_late_P6HB2` 的 `hcenE` 槽；剩余 binder =
`hcapWL hfoot htrans hrerunE8`（逐字不变）+ `hCs1 hCs2 hrec`（本 producer 的三个显式 binder）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hrec : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale) :=
  fun hcapWL hfoot htrans hrerunE8 =>
    ObservedHistory.hbd_stage_late_P6HB2 (F := F) (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
      (C1f := C1f) (C2f := C2f) (m := m) (kk := kk) (η₁ := η₁) (C1₁ := C1₁) (C2₁ := C2₁)
      (Ctime₁ := Ctime₁) hcapWL hfoot htrans
      (hcenE_of_noShortcut_P6HE F hε hε' hCs1 hCs2 hrec) hrerunE8

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-! ## 4. G3：ceiling v2 项（占位支配引理，不改 `p6X1std`） -/

namespace GC.LongTime.Ch11

universe u

open GC.GeneralFlow

/-- **ceiling v2 附加项（`C1` 侧，`_P6HE`）**：`p6X1std_C11GT6` 与 collar 常数取 max。**占位**：
冻结 ceiling 仍是 `p6X1std_C11GT6`；本项归 CHAIN/GAPTOP 后继（并入 `hP6b` ceiling v2 时才被消费）。 -/
def p6X1col_P6HE (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X1std_C11GT6.{u} Γ) (capCollarCs_P6HE.{u} Γ.epsilon)

/-- **ceiling v2 附加项（`C2` 侧）**。 -/
def p6X2col_P6HE (Γ : ClosedBirthConstants) : ℝ :=
  max (p6X2std_C11GT6.{u} Γ) (capCollarCs_P6HE.{u} Γ.epsilon)

/-- collar 常数 `≤ max (p6CapCs ε) (capCollarCs ε)`（占位形：因两常数无大小关系，只能经 max 支配）。 -/
theorem capCollarCs_le_max_P6HE (ε : ℝ) :
    capCollarCs_P6HE.{u} ε ≤ max (p6CapCs_C11GT6.{u} ε) (capCollarCs_P6HE.{u} ε) :=
  le_max_right _ _

/-- 旧标准项被 v2 项支配（既有 `capCs_le_C1P6_C11CL2` 等在 v2 下继续成立）。 -/
theorem p6X1std_le_col_P6HE (Γ : ClosedBirthConstants) :
    p6X1std_C11GT6.{u} Γ ≤ p6X1col_P6HE.{u} Γ :=
  le_max_left _ _

theorem p6X2std_le_col_P6HE (Γ : ClosedBirthConstants) :
    p6X2std_C11GT6.{u} Γ ≤ p6X2col_P6HE.{u} Γ :=
  le_max_left _ _

/-- **`hCs1` 在 ceiling v2 处**：`capCollarCs ε ≤ C1P6 p6X1col Γ`（`ε := Γ.epsilon`）。 -/
theorem capCollarCs_le_C1P6col_P6HE (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1col_P6HE.{u} Γ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- **`hCs2` 在 ceiling v2 处**：`capCollarCs ε ≤ C2P6 p6X2col Γ`。 -/
theorem capCollarCs_le_C2P6col_P6HE (Γ : ClosedBirthConstants) :
    capCollarCs_P6HE.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2col_P6HE.{u} Γ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- v2 ceiling 支配 v1 ceiling（旧消费者不受影响）。 -/
theorem C1P6_std_le_col_P6HE (Γ : ClosedBirthConstants) :
    C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ≤ C1P6_C11GT6.{u} p6X1col_P6HE.{u} Γ :=
  max_le_max le_rfl (p6X1std_le_col_P6HE Γ)

theorem C2P6_std_le_col_P6HE (Γ : ClosedBirthConstants) :
    C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ≤ C2P6_C11GT6.{u} p6X2col_P6HE.{u} Γ :=
  max_le_max le_rfl (p6X2std_le_col_P6HE Γ)

end GC.LongTime.Ch11
