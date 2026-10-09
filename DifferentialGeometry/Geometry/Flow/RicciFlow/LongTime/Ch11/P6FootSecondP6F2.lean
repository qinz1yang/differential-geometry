import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcenProducerP6HE
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScaleSepP6SS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GoodConstantsP6P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M

/-!
# R-C11-13 D-4 / D-9 第二轮：不带 footprint 的 `hmargin`、event 时刻 ceiling、由 separation 付 `6 < scale`
# （O-CH11-FOOT2 G1 / G2 / G3，后缀 `_P6F2`）

三项都以 selected family 前缀（`hlocBCD.txt` 第 2–35 行逐字：clock、small-seed、`k+1 ≤ R k`、hsel、hgood、
late room、`σ k = time (i k).succ`）为前件。

* **G1 `hmargin_noD_P6F2`**（D-4(i)）：结论 = BCDT `hlocBCD_of_supplies_P6BT` 的 `hmargin` binder **逐字**。
  单 history kernel `hmargin_history_P6F2` 直接调 `surgery_no_shortcut_C11D`（seed crossing 用 hmargin 自带的
  `h1`；坏点保护 `bad_not_mem_innerWindow_P6HE`、种子保护 `exists_seed_not_mem_innerWindow_P6HE`；RHS 换元同
  `hcenE_history_P6HE` 的 `hRHS`）。**没有 footprint `D`、不经 `hcenE(D)`**，所以没有
  `D ← hlocBCD ← hcenE(D)` 的循环。binder：`hCs1 hCs2`（collar 常数，同 HCENP）+ **`hrec6S`**（hrec6 的五合取
  收窄到 selected family，前缀逐字）。`hrec6S_of_hrec6_P6F2`：旧全 family `hrec6`（Tendsto 形）⇒ `hrec6S`。
* **G2 `hceil_event_P6F2`**（D-4(ii)）：结论 = SCALESEP `hscaleSep_of_ceiling_P6SS` 的 `hceil` binder
  **逐字**（`R_k ≤ ρ̃(σ_k)⁻²`，**取在 event 时刻 σ_k**，不是 `T_n`）。证明是 `ceiling_of_bad_P6HP` 的
  S5 逆否核（`canonical_rescale_P6X`，取 `Tn := σ`，不需要 `hanti`）。关键点：`σ_k = time (i k).succ` 时
  `time (activeStage σ_k) = σ_k`，Good 的时间导数分量**空真**，所以 **S11 不需要**；hsel 只否定 spatial witness，
  再经 `hasSpatialCanonicalTimeControl_mono_all_P6P` 降到细元组 `(η₁, C1₁, C2₁)`。binder =
  `hcan₁ hηε hsmall hC1 hC2`，**与 HRESTP/HP2 组装（`hrestP_of_slots_P6HP2`）的
  `hcan₁ hdomF hηε hsmall` 是同一组**：
  元组对齐，不新增 binder。
* **G3 `six_lt_scale_of_sep_P6F2`**（D-9）：单 record kernel `static_scale_gt_of_sep_P6F2`——event-scale
  separation `∀ j, Q_A·R < (1 − 4323 δ_j)·scale_cut_j`（hscaleSep 结论形）+ `recenter_scale_comparison`
  （`Λ δ_j ≤ 1/2`）⇒ `∀ b, Q_A·R/2 < scale_static_b`；取 `Q_A = 12`、`1 ≤ R` 得 `6 < scale`。
  selected-family producer `hrec6S_of_sep_P6F2`：S14（P5L records）+ S1（`hδq`）+ `hceil`（G2）+
  `record_scaleSep_P6SS` ⇒ `hrec6S`，**不用 `hcompat` / `hlateT`**。lateness 只用于与 `c` 无关的阈值（P5L 的 `T`、
  `δ` 小），scale 下界来自 event ceiling（`R_k ≤ ρ̃(σ_k)⁻²` 把 `c_k` 与几何绑在一起）。
  **收窄理由**：全 family 的 `hrec6′` 仍不可无条件证（审稿反例成立）；字面 `(k+1)² ≤ c_k s_k^orig` 需
  `δ(t_k)⁴ ≤ 1/(2(k+1))` 的衰减率（固定 `Q_A` 只给 `Q_A (k+1)/2`），而第 5 合取只要 `6 < scale`，故不需要它。
* consumers：`hcenE_of_noShortcut_sel_P6F2`（HCENP 孪生，`hrec` → `hrec6S`；喂 HB2 的 `hcenE` 槽）、
  闭合形 `hrec6S_of_supplies_P6F2` / `hmargin_of_supplies_P6F2`；`example` 见
  `P6FootSecondConsumerP6F2.lean`（喂 BCDT `hmargin`、SCALESEP `hceil`、HB2 `hcenE`、HP2 元组对齐）。
**PROVISIONAL**：G1 binder `hCs1 hCs2 hrec6S`；G2 binder `hcan₁`（S5 在细元组，owner P6OUTER /
CX-OUTER2，与 HRESTP 同一个）+ 常数比较 `hηε hsmall hC1 hC2`；G3 kernel PROVED，producer binder
`hP5L hδq hceil`（S14 / S1 树内具名供给 + G2）。
陈述由 build-logs/scratch/O-CH11-FOOT2/gen.py 从 `hlocBCD.txt` / BCDT / SCALESEP / HCENP 源文本逐字生成。
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

/-! ## G3 kernel：event-scale separation ⇒ static cap neck scale -/

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **separation ⇒ static scale（PROVED，`_P6F2`）**：cut neck 的 event-scale separation
`Q_A·R < (1 − 4323 δ_j)·scale_j`（hscaleSep 的结论形）与 `Λ δ_j ≤ 1/2` ⇒ 每个 static cap 的 neck scale
`> Q_A·R/2`（`recenter_scale_comparison`：`|s_b/s_j − 1| ≤ Λ δ_j`，`j = b.1.1`）。 -/
theorem static_scale_gt_of_sep_P6F2 (Rc : GeometricCutoffRecord H i pp) {QA R : ℝ}
    (hsep : ∀ j, QA * R < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale)
    (hΛ : ∀ j, pp.recenterConstant * Rc.delta j ≤ 1 / 2) :
    ∀ b : (H.event i).RetainedBoundaryIndex, QA * R / 2 < (Rc.static b).neck.scale := by
  intro b
  have hs0 : 0 < (Rc.neck b.1.1).scale := by
    rw [Rc.scale_eq]
    exact inv_pos.mpr (pow_pos (Rc.nominal_pos _) 2)
  have hd0 := Rc.delta_pos b.1.1
  have h1 : QA * R < (Rc.neck b.1.1).scale :=
    (hsep b.1.1).trans_le (by nlinarith [mul_pos hd0 hs0])
  have h2 : 1 / 2 ≤ (Rc.static b).neck.scale / (Rc.neck b.1.1).scale := by
    have := (abs_le.mp ((Rc.recenter_scale_comparison b).trans (hΛ b.1.1))).1
    linarith
  have h3 : (Rc.neck b.1.1).scale / 2 ≤ (Rc.static b).neck.scale := by
    rw [le_div_iff₀ hs0] at h2
    linarith
  linarith

/-- **`six_lt_scale_of_sep_P6F2`（G3，PROVED）**：`Q_A = 12` 的 separation + `1 ≤ R` + `Λ δ_j ≤ 1/2`
⇒ `∀ b, 6 < scale_static_b`（hrec6 第 5 合取的单 record 形）。 -/
theorem six_lt_scale_of_sep_P6F2 (Rc : GeometricCutoffRecord H i pp) {R : ℝ} (hR : 1 ≤ R)
    (hsep : ∀ j, 12 * R < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale)
    (hΛ : ∀ j, pp.recenterConstant * Rc.delta j ≤ 1 / 2) :
    ∀ b : (H.event i).RetainedBoundaryIndex, 6 < (Rc.static b).neck.scale := by
  intro b
  have := Rc.static_scale_gt_of_sep_P6F2 hsep hΛ b
  linarith

end GeometricCutoffRecord

/-! ## G1 kernel：不带 footprint 的 no-shortcut 距离余量 -/

namespace ObservedHistory

/-- **`hmargin` 的单 history kernel（`_P6F2`）**：record `Rc`（canonical windows、`modelAccuracy ≤ 1/2`、
`transitionEnd + 10 < modelRadius`）、collar witness `hcol`、hsel、种子保护 `hseed` ⇒ 对实际 crossing
`(p', q)`（`HEq y q`）与 seed 跨过 event `i` 的索引证明 `h1 h2`，`∀ δ > 0`，`t → time i.succ⁻` 时
`d_{e⁻,t}(seed, p') ≤ d_{g(σ)}(seed_σ, y) + δ`。= `surgery_no_shortcut_C11D` + `hRHS` 换元；
**无 footprint `D`**。 -/
theorem hmargin_history_P6F2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {pp : CutoffParameters} (Rc : GeometricCutoffRecord H i pp)
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcan : ∀ b, (Rc.static b).hasCanonicalWindow) (hacc : pp.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < pp.modelRadius)
    (hcol : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 ((Rc.static b).window x),
        W.capTubeHasNeckChart ε)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (hσ : (σ : ℝ) = H.time i.succ)
    (hseed : ∀ (b : (H.event i).RetainedBoundaryIndex) (h1 : H.activeStage aSeed ≤ i.succ)
      (h2 : i.succ ≤ H.activeStage Tn), seedTrace.point i.succ h1 h2 ∉ (Rc.static b).window ''
        {x : standardCapWindow pp.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10})
    (y : (H.stageAt σ).Carrier) (hsel : ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y) :
    ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∀ (h1 : H.activeStage aSeed ≤ i.castSucc) (h2 : i.castSucc ≤ H.activeStage Tn) {δ : ℝ},
        0 < δ →
        ∀ᶠ t in 𝓝[<] H.time i.succ,
          riemannianEDistOf (H.stageMetric i.castSucc t) (seedTrace.point i.castSucc h1 h2) p' ≤
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hsT)) y + ENNReal.ofReal δ := by
  intro p' q hyq hcp h1 h2 δ hδ
  have hl : i.succ ≤ H.activeStage Tn :=
    H.le_activeStage Tn i.succ (by rw [← hσ]; exact Subtype.coe_le_coe.mpr hsT)
  have hcs : i.castSucc ≤ i.succ := Fin.castSucc_lt_succ.le
  have hco := seedTrace.crossing i h1 hl
  have hσs : H.activeStage σ = i.succ := H.activeStage_eq_succ_of_time_P6ST4 i σ hσ
  have hσheq : HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
      (H.activeStage_mono hsT)) (seedTrace.point i.succ (h1.trans hcs) hl) :=
    seedTrace.point_heq_P6HE hσs _ _ _ _
  have hnos := H.surgery_no_shortcut_C11D i (fun b => Rc.static b) Rc.old_eq_retained hcan hacc
    hD hco hcp (hseed · (h1.trans hcs) hl) (H.bad_not_mem_innerWindow_P6HE i Rc hcol hσ hsel hyq)
    hδ
  have hRHS : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
      (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y =
      riemannianEDistOf (H.stageMetric i.succ (H.time i.succ))
        (seedTrace.point i.succ (h1.trans hcs) hl) q := by
    rw [H.stageMetric_succ_time_C11G i]
    exact edist_heq_P6ST4 (congrArg H.stage hσs) (H.stageMetric_heq_output_P6ST4 i σ hσ) hσheq hyq
  rw [hRHS]
  exact hnos

end ObservedHistory

/-! ## G1：`hmargin` 逐字（binder `hrec6S`） -/

/-- **`hmargin` producer（G1，PROVISIONAL，`_P6F2`）**：结论 = BCDT `hlocBCD_of_supplies_P6BT` 的 `hmargin`
binder **逐字**（`verify.py` 字节核对）。证明 = HCENP 的 record / collar / 种子保护准备 +
`hmargin_history_P6F2`（直接 `surgery_no_shortcut_C11D`），**无 footprint `D`、不经 `hcenE`**。
binder：`hCs1 hCs2`（collar 常数，同 `hcenE_of_noShortcut_P6HE`）、`hrec6S`（五合取 late records，收窄到
selected family；G3 `hrec6S_of_sep_P6F2` 付）。 -/
theorem hmargin_noD_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hrec6S :
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
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi
  obtain ⟨ε₀, hε₀, hseedprot⟩ := exists_seed_not_mem_innerWindow_P6HE.{u}
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hRcap, hcolev⟩ :=
    GC.LongTime.Ch11.capCollar_of_record_P6HE.{u} hε hε'
  have hrecEv := hrec6S ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi (min (min (1 / 2) ε₀) εcap) Rcap
    (max mcap 2) (lt_min (lt_min (by norm_num) hε₀) hεcap)
  filter_upwards [hrecEv] with k hk
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
  intro p' q hyq hcp h1' h2' δ hδ
  exact (Kh k).hmargin_history_P6F2 (i k) Rc hcan hacc1 hD hcol (haT k) (seedTrace k) (hsT k)
    (has k) (hi k) hseedk (y k) (hsel k) p' q hyq hcp h1' h2' hδ

/-- **旧 `hrec6` ⇒ `hrec6S`（PROVED）**：全 family 的 `hrec6`（`Tendsto (c k · time)` 前提，HCENP binder 形）
在 selected family 上的限制；`Tendsto` 由前缀的 clock / `k+1 ≤ c·Tn` / `1 ≤ aSeed` 推出（同 HCENP 的 `hlate`）。
旧 producer（HREC6 G1b/G1d）因此仍可喂 G1。 -/
theorem hrec6S_of_hrec6_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
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
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi
  refine hrec6 ind c hc i ?_
  refine tendsto_atTop_mono (fun k => ?_)
    ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const two_pos)
  have hck := hc k
  have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
  have hcl := hclock k
  have h1k := h1 k
  have hT := hTc k
  rw [← hi k]
  nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
    mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]

/-! ## G2：event 时刻 ceiling -/

/-- **`hceil` producer（G2，PROVISIONAL，`_P6F2`）**：结论 = SCALESEP `hscaleSep_of_ceiling_P6SS` 的 `hceil`
binder **逐字**（`R_k ≤ ρ̃(σ_k)⁻²`，event 时刻）。若 `R_k > ρ̃(σ_k)⁻²`：S5（`hcan₁`，细元组）经
`canonical_rescale_P6X`（= `ceiling_of_bad_P6HP` 的 S5 逆否核，`Tn := σ`）给 `(η₁, C1₁, C2₁)`
spatial witness；
`σ_k = time (i k).succ` ⇒ `time (activeStage σ_k) = σ_k`，时间导数分量空真（**S11 不需要**）；
`hasSpatialCanonicalTimeControl_mono_all_P6P`（`η₁ ≤ ε < 1/11`、`C1₁ ≤ C1`、`C2₁ ≤ C2`）⇒
Good`(ε, C1, C2, Ctime)`，
与 hsel 矛盾。binder 与 HRESTP/HP2 的 `hcan₁ hdomF hηε hsmall` 同组（元组对齐）。 -/
theorem hceil_event_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    {η₁ C1₁ C2₁ : ℝ}
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hηε : η₁ ≤ ε) (hsmall : ε < 1 / 11) (hC1 : C1₁ ≤ C1) (hC2 : C2₁ ≤ C2) :
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
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹ := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi k
  by_contra hlt
  have hlt' : (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹ <
      metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k) := by
    rw [← hRdef k]
    exact lt_of_not_ge hlt
  obtain ⟨W, hW⟩ := RetainedCoreHistory.canonical_rescale_P6X (F.tower.history (ind k)) (hc k)
    (hcan₁ (ind k)) (σ k) (y k) hlt'
  have hσs : (Kh k).activeStage (σ k) = (i k).succ :=
    (Kh k).activeStage_eq_succ_of_time_P6ST4 (i k) (σ k) (hi k)
  have hb : (Kh k).time ((Kh k).activeStage (σ k)) = (σ k : ℝ) := by rw [hσs, hi k]
  exact hsel k (ObservedHistory.hasSpatialCanonicalTimeControl_mono_all_P6P hηε hsmall hC1 hC2
    le_rfl ⟨⟨W, hW⟩, fun hlt2 _ => absurd hb (ne_of_lt hlt2)⟩)

/-! ## G3：`hrec6S` 由 event-scale separation 付 -/

/-- **`hrec6S` producer（G3，PROVISIONAL，`_P6F2`）**：S14 `LateLinkedRecordsSupply_C11E F q`（固定目标
`(Rcap, εcap, mcap)` 的 linked records，`p.delta = q.delta`、`p.neckRadius = q.neckRadius`、
`p.recenterConstant = q.recenterConstant`）+ S1 `hδq` + event ceiling `hceil`（G2）⇒ `hrec6S`。
record = P5L record 的 `rescale_P6M`；`6 < scale` = `record_scaleSep_P6SS`（`Q_A = 12`，ceiling 在
`σ_k = time (i k).succ`，`δ(t_k) ≤ 1/(8646·13)`）+ `six_lt_scale_of_sep_P6F2`
（`Λ δ_j ≤ Λ δ(t_k) ≤ 1/2`、
`1 ≤ R_k`）。**不用 `hcompat` / `hlateT`**：event time `→ ∞` 只喂 `c` 无关阈值（P5L 的 `T` 与 `δ` 小）。 -/
theorem hrec6S_of_sep_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hceil :
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
        ∀ k, R k ≤ (((q.rescale_P6N (c k) (hc k)).neckRadius (σ k)) ^ 2)⁻¹) :
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
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii i hi εcap Rcap mcap hεcap
  have hceilk := hceil ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
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
  obtain ⟨T, hT⟩ := hP5L Rcap εcap mcap hεcap
  have hΛ : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have hδ₀ : (0 : ℝ) < min (1 / (8646 * (12 + 1))) (1 / (2 * q.recenterConstant)) :=
    lt_min (by norm_num) (by positivity)
  obtain ⟨Tδ, hTδ⟩ := Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hδ₀))
  have hev : ∀ᶠ k in atTop, max T Tδ ≤ (F.tower.history (ind k)).time (i k).succ := by
    filter_upwards [hlate.eventually_ge_atTop (max T Tδ)] with k hk
    have e : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
      mul_div_cancel₀ _ (hc k).ne'
    exact e ▸ hk
  filter_upwards [hev] with k hk
  obtain ⟨p, hpδ, hpρ, -, hprc, hD, hacc, hord, records, hlink⟩ := hT (ind k)
  have hkT : T ≤ (F.tower.history (ind k)).time (i k).succ := (le_max_left _ _).trans hk
  have hkδ : q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
      min (1 / (8646 * (12 + 1))) (1 / (2 * q.recenterConstant)) :=
    hTδ _ ((le_max_right _ _).trans hk)
  refine ⟨p.rescale_P6N (c k) (hc k), (records (i k) hkT).rescale_P6M (c k) (hc k),
    fun b => ?_, hacc, hD, hord, ?_⟩
  · exact ((records (i k) hkT).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _ (hlink (i k) hkT b))
      (c k) (hc k)
  · have et : c k * (Kh k).time (i k).succ = (F.tower.history (ind k)).time (i k).succ :=
      mul_div_cancel₀ _ (hc k).ne'
    have hδt : (p.rescale_P6N (c k) (hc k)).delta ((Kh k).time (i k).succ) =
        q.delta ((F.tower.history (ind k)).time (i k).succ) := by
      change p.delta (c k * (Kh k).time (i k).succ) = _
      rw [hpδ, et]
    have eρ : (p.rescale_P6N (c k) (hc k)).neckRadius =
        (q.rescale_P6N (c k) (hc k)).neckRadius := by
      funext t
      change p.neckRadius (c k * t) / Real.sqrt (c k) = q.neckRadius (c k * t) / Real.sqrt (c k)
      rw [hpρ]
    have hc1 : R k ≤ ((p.rescale_P6N (c k) (hc k)).neckRadius ((Kh k).time (i k).succ) ^ 2)⁻¹ := by
      rw [eρ, ← hi k]
      exact hceilk k
    have hc2 : (p.rescale_P6N (c k) (hc k)).delta ((Kh k).time (i k).succ) ≤
        1 / (8646 * (12 + 1)) := by
      rw [hδt]
      exact hkδ.trans (min_le_left _ _)
    have hsep := ((records (i k) hkT).rescale_P6M (c k) (hc k)).record_scaleSep_P6SS
      (QA := 12) (by norm_num) hc1 hc2
    have hΛδ : ∀ j, (p.rescale_P6N (c k) (hc k)).recenterConstant *
        ((records (i k) hkT).rescale_P6M (c k) (hc k)).delta j ≤ 1 / 2 := by
      intro j
      have hj : ((records (i k) hkT).rescale_P6M (c k) (hc k)).delta j ≤
          (p.rescale_P6N (c k) (hc k)).delta ((Kh k).time (i k).succ) :=
        ((records (i k) hkT).rescale_P6M (c k) (hc k)).delta_le j
      have hj0 := ((records (i k) hkT).rescale_P6M (c k) (hc k)).delta_pos j
      rw [hδt] at hj
      have hq2 : q.delta ((F.tower.history (ind k)).time (i k).succ) ≤
          1 / (2 * q.recenterConstant) := hkδ.trans (min_le_right _ _)
      change p.recenterConstant * _ ≤ _
      rw [hprc]
      have h3 := (le_div_iff₀ (by positivity)).1 (hj.trans hq2)
      nlinarith
    have hR1 : (1 : ℝ) ≤ R k := by
      have := hRr k
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    exact ((records (i k) hkT).rescale_P6M (c k) (hc k)).six_lt_scale_of_sep_P6F2 hR1
      hsep.2 hΛδ

/-- **闭合形（G2 ∘ G3，PROVISIONAL）**：S14 + S1 + `hcan₁`（细元组 S5）+ 常数比较 ⇒ `hrec6S`。 -/
theorem hrec6S_of_supplies_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    {η₁ C1₁ C2₁ : ℝ}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hηε : η₁ ≤ ε) (hsmall : ε < 1 / 11) (hC1 : C1₁ ≤ C1) (hC2 : C2₁ ≤ C2) :
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
        ∀ (εcap Rcap : ℝ) (mcap : ℕ), 0 < εcap →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          (∀ b, (Rc.static b).hasCanonicalWindow) ∧ pp.modelAccuracy ≤ εcap ∧
            Rcap ≤ pp.modelRadius ∧ mcap ≤ pp.modelOrder ∧ ∀ b, 6 < (Rc.static b).neck.scale :=
  hrec6S_of_sep_P6F2 (Ctime := Ctime) hP5L hδq (hceil_event_P6F2 hcan₁ hηε hsmall hC1 hC2)

/-- **闭合形（G1 ∘ G2 ∘ G3，PROVISIONAL）**：`hmargin` 逐字 ⇐ `hCs1 hCs2` + S14 + S1 + `hcan₁` + 常数比较。
无 footprint、无 `hcenE`、无 `hcompat`。 -/
theorem hmargin_of_supplies_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters}
    {η₁ C1₁ C2₁ : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hηε : η₁ ≤ ε) (hC1 : C1₁ ≤ C1) (hC2 : C2₁ ≤ C2) :
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
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ :=
  hmargin_noD_P6F2 (Ctime := Ctime) F hε hε' hCs1 hCs2
    (hrec6S_of_supplies_P6F2 hP5L hδq hcan₁ hηε hε' hC1 hC2)

/-! ## consumer 定理：`hcenE` 孪生（`hrec` → `hrec6S`） -/

/-- **`hcenE` 孪生（`_P6F2`）**：`hcenE_of_noShortcut_P6HE` 的结论**逐字**（= HB2 `hcenE` binder），只把全 family
`hrec`（Tendsto 形，第 5 合取对任意 `c` 不可付）换成 selected-family **`hrec6S`**（G3 付）。证明同 HCENP。 -/
theorem hcenE_of_noShortcut_sel_P6F2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ}
    (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hrec6S :
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
  obtain ⟨ε₀, hε₀, hseedprot⟩ := exists_seed_not_mem_innerWindow_P6HE.{u}
  obtain ⟨Rcap, mcap, εcap, -, hεcap, hRcap, hcolev⟩ :=
    GC.LongTime.Ch11.capCollar_of_record_P6HE.{u} hε hε'
  have hrecEv := hrec6S ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi (min (min (1 / 2) ε₀) εcap) Rcap
    (max mcap 2) (lt_min (lt_min (by norm_num) hε₀) hεcap)
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
