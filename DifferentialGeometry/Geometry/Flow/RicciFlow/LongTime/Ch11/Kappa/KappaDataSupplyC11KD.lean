import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.HistorySliceScalarBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.S8WireC11V4

set_option autoImplicit false

/-!
# 局部 κ 线端到端的数据前提（S-CH11-KDATA G2，后缀 `_C11KD`）

`nonempty_pre841Data_of_native_C11Q2`（`Kappa/KappaEndToEndC11Q2`）的数据 binder
`N / hκ / hδ / hacc / hsmallScale` 由 narrow tuple（`w1_params_of_preparedSpatialChain_C11P2` /
`exists_w1_params_timeDerivative_C12X` 的输出合取项）与树内引理给出，使端到端只剩
`hW`（WeightedMinBound）、`hB`（block）、`hscale`（δ₀ 尺度）三条 K 链前提。

* `history_curvatureLower_of_records_C11KD`：records ⇒ `a > 0`，所有 history 的 stage metric 在年龄
  `a + t` 处于 fixed HI region，且 `R ≥ -3/(2(t + a/2))`。`curvatureLower_of_records_C11S` 只有
  `postMetric` 形，`stageMetric_scalarLower_C11S` 是 private，这里用 `exists_history_pinching_P6A` 的
  HI 与公开的 `FILL910.A03a_stageMetric_scalar_lower`（`c = a/2`）重证 history 形。
* `nativeDataOfSupplies_C11KD`：narrow tuple 的 `(F, q, records)` + S3 / S4 / S5 / S9 / S11 的数据合取项
  ⇒ `Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)`；`params = q`、`records`、`Ctime`
  逐字（`rfl` 引理 `nativeDataOfSupplies_params_C11KD` 等）。pinching / scalar_lower 取上一条的 shift
  （`a` 与 `a/2`）。
* `blockKappa_C11KD`：block 的体积常数 `κ₀(A) = (max A 1)⁻¹ e⁻⁵⁷ / (512·100³)`（KAPPA2 Q3-G3 的 URE
  `ureBlockKappa_C11Q3`），`blockKappa_pos_C11KD` 给端到端的 `hκ`。
* `hsmallScale_of_wideSupply_C11KD`：Q3 小尺度前提（端到端的 `hsmallScale`，`nr = q.neckRadius`）⇐
  K 的 `LocalKappaWideSupply_C11Q`（`localKappaWideSupply_of_native_C11Q2` 的结论）+ S7（对角 `α`）+
  P3 / hprof + records 的 canonical window。与 SMALLVOL4 `smallVolWindow_of_hext_C11V4` 同一条链，
  止于 `hsmall_of_wide_window_late_C11V3` 的 Q3 `hsmall` 形（`nr' = nr ∘ max · 0` 换回 `nr`）。
  `ε₀` 只依赖 `(ε, C1, C2, N(P))`，在 `g F q` 之前（GAP-2 的量词次序）；
  `q.modelAccuracy ≤ ε₀` 是显式 binder（outer 取 `εReserve := min εProf ε₀`）。
* 端到端的 `hδ` 取 `δ := q.delta`（`le_rfl`），`hacc` 取 `largerBallAccuracySupply_diagonal_C11S`
  （`α := diagonalAccuracy_C11S q.delta`），在 G3 文件里接线。
-/

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. history 形的 HI + 标量下界 -/

/-- **history 形 pinching + scalar lower**：records ⇒ `a > 0`，每个 history 的 `stageMetric` 在
年龄 `a + t` 处于 fixed HI region，且 `R ≥ -3/(2(t + a/2))`。`a` 由初始度量紧性取，不依赖 `n`。 -/
theorem history_curvatureLower_of_records_C11KD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) :
    ∃ a : ℝ, 0 < a ∧ ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
        InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a + t) x ∧
          -3 / (2 * ((t : ℝ) + a / 2)) ≤
            metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
  obtain ⟨a, ha, hfixed, hscalar⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a, ha, ?_⟩
  intro n H t x
  have hzero := (F.tower.initial n).fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hscalar
  have hpinching := H.fixedHamiltonIveyRegion_and_scalar_lower (records n) ha hzero.1 hzero.2
  have hscalarZero : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (a / 2)) ≤ metricScalarAt (H.initialMetric 0) y := by
    intro y
    simpa only [show 2 * (a / 2) = a by ring] using hzero.2 y
  exact ⟨(hpinching.1 (H.activeStage t) t (H.activeStage_mem t) x).1,
    FILL910.A03a_stageMetric_scalar_lower H (records n) (half_pos ha) hscalarZero
      (H.activeStage t) t (H.activeStage_mem t) x⟩

/-- `scalar_lower` 的 shift `a/2` 里的 `a`（pinching 的 shift），由树内定理选出。 -/
def curvatureShift_C11KD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) : ℝ :=
  (history_curvatureLower_of_records_C11KD F records).choose

/-! ## 2. `N`：native 数据 ⇐ narrow tuple 的数据合取项 -/

/-- **`Pre841NativeData_C11K` ⇐ narrow tuple**：`params = q`、`records`、`Ctime` 逐字；
S3 `canonical_windows`、S1 `delta_*`、S2 `radius_antitone`、S4 常数、S5 `canonical`、S9
`recent_cutoff_smallness`、S11 时间导数控制是 tuple（含 `exists_w1_params_timeDerivative_C12X`）的
合取项；`scalar_lower / pinching` 取 `history_curvatureLower_of_records_C11KD` 的 shift。 -/
def nativeDataOfSupplies_C11KD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hδanti : AntitoneOn q.delta (Ici 0)) (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hwin : CanonicalWindowsSupply_C11S records)
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hP2 : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hrecent : RecentCutoffSupply_C11S records) :
    Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory) where
  params := q
  records := records
  canonical_windows := hwin
  radius_antitone := hρanti
  delta_antitone := hδanti
  delta_tendsto := hδlim
  epsilon := ε
  epsilon_pos := hconst.1
  epsilon_small := hconst.2.1
  C1 := C1
  C2 := C2
  C1_ge_one := hconst.2.2.1
  C2_ge_one := hconst.2.2.2
  canonical := hcan
  Ctime := Ctime
  time_derivative_event := hP2.1
  time_derivative_final := hP2.2
  scalarShift := curvatureShift_C11KD F records / 2
  scalarShift_pos := half_pos (history_curvatureLower_of_records_C11KD F records).choose_spec.1
  scalar_lower := fun n t x =>
    ((history_curvatureLower_of_records_C11KD F records).choose_spec.2 n t x).2
  pinchingShift := curvatureShift_C11KD F records
  pinchingShift_pos := (history_curvatureLower_of_records_C11KD F records).choose_spec.1
  pinching := fun n t x =>
    ((history_curvatureLower_of_records_C11KD F records).choose_spec.2 n t x).1
  recent_cutoff_smallness := hrecent

/-- `N.params = q`（`rfl`）：端到端的 `N.params.neckRadius / delta` 即 `q.neckRadius / delta`。 -/
theorem nativeDataOfSupplies_params_C11KD {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) (hρanti : AntitoneOn q.neckRadius (Ici 0))
    (hδanti : AntitoneOn q.delta (Ici 0)) (hδlim : Tendsto q.delta atTop (𝓝 0))
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hwin : CanonicalWindowsSupply_C11S records)
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hP2 : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hrecent : RecentCutoffSupply_C11S records) :
    (nativeDataOfSupplies_C11KD F q records ε C1 C2 Ctime hρanti hδanti hδlim hconst hwin hcan hP2
      hrecent).params = q :=
  rfl

/-! ## 3. `hκ`：block 的体积常数 -/

/-- block 的体积常数 `κ₀(A) = (max A 1)⁻¹ e⁻⁵⁷ / (512·100³)`（逐字同 KAPPA2 Q3-G3 的
`ureBlockKappa_C11Q3`，`A < 1` 借 `A' = max A 1`；G3 文件里有 `rfl` 对齐）。 -/
def blockKappa_C11KD (A : ℝ) : ℝ :=
  (max A 1)⁻¹ * Real.exp (-57) / (512 * (100 : ℝ) ^ 3)

/-- 端到端的 `hκ`：`blockKappa_C11KD` 对 `A > 0` 为正。 -/
theorem blockKappa_pos_C11KD : ∀ A : ℝ, 0 < A → 0 < blockKappa_C11KD A := by
  intro A _
  have h : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold blockKappa_C11KD
  positivity

/-! ## 4. `hsmallScale`：Q3 小尺度前提 -/

/-- **端到端的 `hsmallScale`**（`nr = q.neckRadius`，`κ'` 存在）：K 的 wide 供给 + S7（对角 `α`）+
P3 / hprof + records 的 canonical window + `HistoryCanonicalSupply` ⇒ Q3 `hsmall`。
`ε₀` 只依赖 `(ε, C1, C2, N(P))`；`q.modelAccuracy ≤ ε₀` 为显式 binder（GAP-2）。 -/
theorem hsmallScale_of_wideSupply_C11KD (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A : ℝ}, 0 < A →
      CollarWindowSupply_C11E.{u} q → ModelConstraintsSupply_C11E q εProf_C11E.{u} →
      q.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, CanonicalWindowsSupply_C11S records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      ∃ κ' : ℝ, 0 < κ' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) →
          2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 < ρ' → ρ' < q.neckRadius v / 100 → ρ' < r / 100 →
            H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨N, hN, hdeg⟩ := exists_stageDegreeBound_uniform_C11V4.{u} P
  obtain ⟨ε₀, hε₀, hE⟩ := hsmall_of_wide_window_late_C11V3.{u}
    (4 * StandardCap.transitionEnd + 6) le_rfl ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F q A hA hP3 hprof hq records hwin hδanti hρanti hcanon hwide
  have hD : 4 * StandardCap.transitionEnd + 6 ≤ q.modelRadius :=
    four_transitionEnd_le_modelRadius_C11V3 hP3
  have hS7 := largerBallAccuracySupply_diagonal_C11S q hδanti
  obtain ⟨c, c', hc, hc', hHI, hlow⟩ := history_HI_and_lower_of_records_C11V3 records
  have hcomp := hcomp_late_of_HI_C11V3 (nr := q.neckRadius) (M := q.neckRadius 0)
    (q.neckRadius_pos 0 le_rfl) (fun s hs => hρanti (Set.mem_Ici.mpr le_rfl) hs hs) hc hc' hHI hlow
  obtain ⟨T₀, hcan⟩ := hcan_late_of_canonicalSupply_C11V3 hρanti hcanon hcomp
  obtain ⟨κ, hκ, hL⟩ := wideLate_of_wideSupply_C11V3 hS7
    (localKappaWideSupply_clamp_C11V3 hwide) hA
  obtain ⟨κ', hκ', T, hT, hK⟩ := hE (nr := fun s => q.neckRadius (max s 0))
    (M := q.neckRadius 0) hA hκ (nr_clamp_le_C11V3 hρanti)
    (wideWindow_of_wideLate_C11V2 (F := F) (nr := fun s => q.neckRadius (max s 0)) (κ := κ) hA
      hL)
    (hcapS_restrict_of_records_C11V4 records hwin hq hprof.2.1 hD)
    ⟨T₀, by
      intro n H v v' hT0 hv'v w s hs hsnr hvs hcont
      have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
      exact hcan n v v' hT0 hv'v w s hs (by simpa only [hmax] using hsnr) hvs hcont⟩
    (hdeg F)
  refine ⟨κ', hκ', T, hT, ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ' hρnr hρr
    hball
  have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
  exact hK n t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ'
    (by simpa only [hmax] using hρnr) hρr hball

/-- **GAP-2 的常数 `ε₀(ε, C1, C2, N(P))`**：`hsmallScale_of_wideSupply_C11KD` 里存在的 `ε₀`
（`Classical.choose`）。显式 binder 写作 `q.modelAccuracy ≤ epsilon0_C11KD ε C1 C2 P`。 -/
def epsilon0_C11KD (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) : ℝ :=
  (hsmallScale_of_wideSupply_C11KD.{u} ε C1 C2 P).choose

theorem epsilon0_pos_C11KD (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    0 < epsilon0_C11KD ε C1 C2 P :=
  (hsmallScale_of_wideSupply_C11KD.{u} ε C1 C2 P).choose_spec.1

/-- **consumer**：`nr = q.neckRadius` 的 window（端到端里 `localKappaWindow_of_late_P6B` 给的）+ 本定理的
Q3 `hsmallScale` ⇒ `nr := 0` window（`localKappaWindow_zero_of_window_and_small_C11V`，正是
`nonempty_pre841Data_of_native_C11Q2` 的最后一步用法）。 -/
example (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {A κ₁ : ℝ},
      0 < A → 0 < κ₁ → CollarWindowSupply_C11E.{u} q →
      ModelConstraintsSupply_C11E q εProf_C11E.{u} → q.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, CanonicalWindowsSupply_C11S records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LocalKappaWindowAt_P6B F q.neckRadius A κ₁ →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := hsmallScale_of_wideSupply_C11KD.{u} ε C1 C2 P
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F q A κ₁ hA hκ₁ hP3 hprof hq records hwin hδanti hρanti hcanon hwide hW
  obtain ⟨κ', hκ', hsmall⟩ := hE hA hP3 hprof hq records hwin hδanti hρanti hcanon hwide
  exact ⟨min κ₁ κ', lt_min hκ₁ hκ',
    localKappaWindow_zero_of_window_and_small_C11V hW hsmall⟩

end GC.LongTime.Ch11
