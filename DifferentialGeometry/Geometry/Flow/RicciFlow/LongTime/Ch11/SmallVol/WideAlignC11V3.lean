import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallAssemblyC11V2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaContractsC11Q
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeneralInitialBound

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL3 G1：`LocalKappaWideSupply_C11Q` → SMALLVOL2 G2 的 wide late 前提（`_C11V3`）

KAPPA（`Kappa/KappaContractsC11Q`）冻结的 `LocalKappaWideSupply_C11Q F δ α nr`（accuracy 形，
`∀ A L > 0, ∃ κ > 0`，上沿 `L r`）与 SMALLVOL2 G2 `wideWindow_of_wideLate_C11V2` 的 wide late **展开**前提
（放大因子 `A' = 51200 e⁵⁷ A`、`L = 100(A+1)`、时间下界 `T ≤ t` 代替 accuracy）之间只差 S7 envelope 一步
（P6B `localKappaLateAt_of_envelope_P6B` 的 wide 版，`T = A'`，P6A `accuracy_on_late_half_P6A`）：
* `wideLate_of_wideSupply_C11V3`：`LocalKappaWideSupply_C11Q` + S7 ⇒ G2 的 wide late 展开前提（∃ κ），
  **K → G2 方向可证**；反向（G2 展开形 ⇒ accuracy 形）**不成立也不需要**——展开形多了时间下界
  `T ≤ t`、少了 accuracy 前提，只是 K 的 late 特化。
* `localKappaWindow_zero_of_wideSupply_C11V3`：G2 端到端定理以 `LocalKappaWideSupply_C11Q` 为起点
  （`nr ≤ M`、`hcapS`、`hcan`、`hdeg` 仍是显式前提，对齐见 `Surgery…` 之后各引理与
  `docs/geometrization/chapter8/CH11-SMALLVOL-ALIGN-20261007.md`）；
* consumer：同上 ⇒ `tracedKappa_of_window_P6B` 的 `hW`。
-/

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **K → G2 的 wide late 展开前提**：`LocalKappaWideSupply_C11Q` + S7 ⇒ 对每个 `A > 0`
`∃ κ > 0, ∃ T > 0,`（G2 `wideWindow_of_wideLate_C11V2` 的 `hL`）。取 `A' = 51200 e⁵⁷ A`、
`L = 100(A+1)`、`T = A'`；`T ≤ t` 时 accuracy 前提由 P6A `accuracy_on_late_half_P6A` 自动成立。 -/
theorem wideLate_of_wideSupply_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (h : LocalKappaWideSupply_C11Q F δ α nr)
    {A : ℝ} (hA : 0 < A) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (51200 * Real.exp 57 * A * r),
        ∀ ρ' : ℝ, nr t / 100 ≤ ρ' → ρ' ≤ 100 * (A + 1) * r →
          H.isParabolicallyRmControlledBall t x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ρ' := by
  have hA' : 0 < 51200 * Real.exp 57 * A := by positivity
  obtain ⟨κ, hκ, hK⟩ := h _ (100 * (A + 1)) hA' (by positivity)
  refine ⟨κ, hκ, 51200 * Real.exp 57 * A, hA', ?_⟩
  intro n H t p r hT hr hsm hvol x hx ρ' hlow hup hball
  exact hK n t p r hr (accuracy_on_late_half_P6A hacc hA' hT) hsm hvol x hx ρ' hlow hup hball

/-- **端到端（window 形，K 链起步）**：`LocalKappaWideSupply_C11Q` + S7 + `nr ≤ M` + G2 的三个
Q3 前提（`hcapS`、`hcan`、`hdeg`）⇒ `∃ κ'' > 0, LocalKappaWindowAt_P6B F (fun _ => 0) A κ''`。 -/
theorem localKappaWindow_zero_of_wideSupply_C11V3 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ} {A M : ℝ}, 0 < A → (∀ s, nr s ≤ M) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α nr →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
          ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
            (S : (H.event i).PresentedStaticCap fixed D m η b),
            η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow) →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ v v' : Icc (0 : ℝ) H.horizon, v' ≤ v → ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
            V.capTubeHasNeckChart ε) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wide_window_C11V2.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α nr A M hA hnrM hacc hwide hcapS hcan hdeg
  obtain ⟨κ, hκ, hL⟩ := wideLate_of_wideSupply_C11V3 hacc hwide hA
  exact hE hA hκ hnrM (wideWindow_of_wideLate_C11V2 hA hL) hcapS hcan hdeg

/-! ## Q3 前提对齐：`nr ≤ M`、`hcapS`、`hdeg`（`N`）、`hcan` -/

/-- **`nr` 的钳位**：`nr' s := nr (max s 0)` 在 `s ≥ 0` 处等于 `nr`，且 `AntitoneOn nr (Ici 0)` 时对**全部**
`s : ℝ` 有 `nr' s ≤ nr 0`（G2 的 `∀ s, nr s ≤ M` 量化了负时刻，profile 只控制 `s ≥ 0`）。 -/
theorem nr_clamp_le_C11V3 {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) (s : ℝ) :
    (fun s' => nr (max s' 0)) s ≤ nr 0 :=
  hanti (le_refl (0 : ℝ)) (le_max_right s 0) (le_max_right s 0)

/-- K 的 wide 供给对 `nr` 钳位不变（`t : Icc 0 horizon` 处 `max t 0 = t`）。 -/
theorem localKappaWideSupply_clamp_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : LocalKappaWideSupply_C11Q F δ α nr) :
    LocalKappaWideSupply_C11Q F δ α (fun s => nr (max s 0)) := by
  intro A L hA hL
  obtain ⟨κ, hκ, hK⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  have hmax : max (t : ℝ) 0 = t := max_eq_left t.2.1
  exact hK n t p r hr hacc hsmall hvol x hx ρ' (by simpa only [hmax] using hlow) hup hball

/-- **`hdeg`（`N`）**：`N` 不在 profile 里，但**不需要** `InCutoffClass`：树内无条件
`initial_finite_freeFactor_bound P`（Kneser 型有限自由因子界）+ `retained_history_freeFactor`
（每个 retained history 的 stage 的 π₁ 是初始 π₁ 的自由因子，只需 `F.tower.initial n`）+
`stage_degree_of_freeFactor_ancestry`。注意 `N` 依赖 `P`（故 G2 的 `ε₀(N)` 与
`pBase.modelAccuracy` 须在 `P` 之后选）。 -/
theorem exists_stageDegreeBound_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) :
    ∃ N : ℕ, 0 < N ∧
      ∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N := by
  obtain ⟨N, hN, hb⟩ := GC.GeneralFlow.initial_finite_freeFactor_bound P
  exact ⟨N, hN, fun n j => GC.GeneralFlow.stage_degree_of_freeFactor_ancestry N hb
    (fun q => GC.GeneralFlow.retained_history_freeFactor (F.tower.history n) (F.tower.initial n) j
      q)⟩

/-- P3 的 collar 条款 `capWindowRadius + 1 ≤ modelRadius` ⇒ G1 的 `D` 下界
`4·transitionEnd + 6 ≤ modelRadius`（`capWindowRadius_C11E = 64(transitionEnd + 2002) + 1`）。 -/
theorem four_transitionEnd_le_modelRadius_C11V3 {q : CutoffParameters}
    (h : CollarWindowSupply_C11E.{u} q) : 4 * StandardCap.transitionEnd + 6 ≤ q.modelRadius := by
  have hte := StandardCap.transitionEnd_pos
  have h2 := h.2
  unfold capWindowRadius_C11E at h2
  linarith

/-- **`hcapS`**：profile / narrow tuple 的 records 给 `∀ n i b` 的 canonical window
（`canonical_windows`），静态帽数据取 `(records n i).static b`（`fixed = q.fixed`、`m = q.modelOrder`、
`η = q.modelAccuracy`、`D = q.modelRadius`）。**不比 profile 强**：多出的只有三个参数前提
`q.modelAccuracy ≤ ε₀`、`2 ≤ q.modelOrder`、（调用处）`4·transitionEnd + 6 ≤ q.modelRadius`。 -/
theorem hcapS_of_records_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow) {ε₀ : ℝ}
    (hacc : q.modelAccuracy ≤ ε₀) (hord : 2 ≤ q.modelOrder) :
    ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed q.modelRadius m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow :=
  fun n i b => ⟨q.fixed, q.modelOrder, q.modelAccuracy, (records n i).static b, hacc, hord,
    hwin n i b⟩

/-- **`hcan`（阈值 `s < nr v/50`）**：`HistoryCanonicalSupply_C11S F nr ε C1 C2`（narrow tuple 输出，
scalar 阈值 `R > nr(t)⁻²`）+ `nr` 单调不增 + **`|Rm|`-vs-`R` 比较 `hcomp`**（`|Rm| = s⁻²`、`s < nr v'/50`
时 `s⁻² ≤ 2500·R`，Hamilton–Ivey 型，**不在树内现成**）⇒ G2 的 `hcan`。`nr` 单调不增使
`s < nr v/50 ⇒ s < nr v'/50`（`v' ≤ v`），所以不需要改成接触时刻形；`hcomp` 即精确缺口。 -/
theorem hcan_of_canonicalSupply_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {ε C1 C2 : ℝ}
    (hanti : AntitoneOn nr (Ici 0))
    (hcanon : HistoryCanonicalSupply_C11S F nr ε C1 C2)
    (hcomp : ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
        0 < s → s < nr v' / 50 →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
          (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
        (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) :
    ∀ n, let H := (F.tower.history n).toHistory;
      ∀ v v' : Icc (0 : ℝ) H.horizon, v' ≤ v → ∀ (w : (H.stageAt v').Carrier) (s : ℝ),
        0 < s → s < nr v / 50 → (v : ℝ) - s ^ 2 ≤ v' →
        s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
          (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
        ∃ V : SpatialCanonicalWitness (H.stageMetric (H.activeStage v') v') ε C1 C2 w,
          V.capTubeHasNeckChart ε := by
  intro n H v v' hv'v w s hs hsnr hvs hcont
  have hnr : nr v ≤ nr v' := hanti v'.2.1 v.2.1 hv'v
  have hsnr' : s < nr v' / 50 := lt_of_lt_of_le hsnr (by linarith)
  have h1 := hcomp n v' w s hs hsnr' hcont
  refine hcanon n v' w ?_
  have h50 : 50 * s < nr v' := by linarith
  have hlt : (50 * s) ^ 2 < nr v' ^ 2 := pow_lt_pow_left₀ h50 (by positivity) two_ne_zero
  have hinv : (nr v' ^ 2)⁻¹ < ((50 * s) ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) hlt
  have he : ((50 * s) ^ 2)⁻¹ = (s⁻¹) ^ 2 / 2500 := by
    field_simp
    ring
  rw [he] at hinv
  have hR : (s⁻¹) ^ 2 / 2500 ≤ metricScalarAt (H.stageMetric (H.activeStage v') v') w := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  exact hinv.trans_le hR

/-- **端到端（narrow tuple 形，K 链起步，无 `M`）**：narrow tuple 的 `(F, q, records)` 数据 +
`LocalKappaWideSupply_C11Q F δ α q.neckRadius` + S7，对齐 G2 的 Q3 前提：
* `nr ≤ M`：`AntitoneOn q.neckRadius (Ici 0)` 给 `M = q.neckRadius 0`（`nr` 钳位，见
  `nr_clamp_le_C11V3`）；
* `hcapS`：`hcapS_of_records_C11V3`（`D = q.modelRadius`）；
* `hcan`：`hcan_of_canonicalSupply_C11V3`（`HistoryCanonicalSupply_C11S` + 单调 + `hcomp`）；
* `hdeg`：`N` 作显式前提（`exists_stageDegreeBound_C11V3` 无条件给出）。
`ε₀` 依赖 `(D, ε, C1, C2, N)`，故 `q.modelAccuracy ≤ ε₀` 是 `pBase` 的额外参数约束。 -/
theorem localKappaWindow_zero_of_narrowTuple_C11V3 (D : ℝ)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < q.neckRadius v' / 50 →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wideSupply_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc' hord records hwin hanti hcanon hcomp hdeg hacc hwide
  have hcan := hcan_of_canonicalSupply_C11V3 hanti hcanon hcomp
  subst hDq
  exact hE (nr := fun s => q.neckRadius (max s 0)) (M := q.neckRadius 0) hA
    (nr_clamp_le_C11V3 hanti) hacc (localKappaWideSupply_clamp_C11V3 hwide)
    (hcapS_of_records_C11V3 records hwin hacc' hord)
    (by
      intro n H v v' hv'v w s hs hsnr hvs hcont
      have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
      exact hcan n v v' hv'v w s hs (by simpa only [hmax] using hsnr) hvs hcont)
    hdeg

/-- **端到端 consumer**（`LocalKappaWideSupply_C11Q` ⇒ `nr := 0` window ⇒ M8 bridge）：
K 链的 wide 供给 + narrow tuple 数据 + Q3 前提 ⇒ `tracedKappa_of_window_P6B` 所需的
`LocalKappaWindowAt_P6B F (fun _ => 0) A κ''`，并实际喂给 `tracedKappa_of_window_P6B`。 -/
example (D : ℝ) (hD : 4 * StandardCap.transitionEnd + 6 ≤ D) (ε C1 C2 : ℝ) (N : ℕ)
    (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {q : CutoffParameters} {A : ℝ}, 0 < A →
      q.modelRadius = D → q.modelAccuracy ≤ ε₀ → 2 ≤ q.modelOrder →
      ∀ records : CutoffRecords_C11S F q,
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) →
      AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n, let H := (F.tower.history n).toHistory;
        ∀ (v' : Icc (0 : ℝ) H.horizon) (w : (H.stageAt v').Carrier) (s : ℝ),
          0 < s → s < q.neckRadius v' / 50 →
          s ^ 4 * normSq0S (H.stageMetric (H.activeStage v') v') w 4
            (metricRm04At (H.stageMetric (H.activeStage v') v') w) = 1 →
          (s⁻¹) ^ 2 ≤ 2500 * metricScalarAt (H.stageMetric (H.activeStage v') v') w) →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LargerBallAccuracySupply_C11S δ α → LocalKappaWideSupply_C11Q F δ α q.neckRadius →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_narrowTuple_C11V3.{u} D hD ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ α q A hA hDq hacc hord records hwin hanti hcanon hcomp hdeg hS7 hwide
  obtain ⟨κ'', -, hW0⟩ := hE hA hDq hacc hord records hwin hanti hcanon hcomp hdeg hS7 hwide
  have := tracedKappa_of_window_P6B hW0
  trivial

/-- enhanced `hext` 里的 `LinkedWindowsSupply_C11E records`（S10 / P1）蕴含 `hcapS` 要的
`∀ n i b, hasCanonicalWindow`（`linkedCanonicalWindow_hasCanonicalWindow_C11E`）。 -/
theorem hwin_of_linkedWindows_C11V3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    (h : LinkedWindowsSupply_C11E records) :
    ∀ n i b, ((records n i).static b).hasCanonicalWindow :=
  fun n i b => linkedCanonicalWindow_hasCanonicalWindow_C11E _ (h n i b)

end GC.LongTime.Ch11
