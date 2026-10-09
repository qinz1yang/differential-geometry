import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier

set_option autoImplicit false

/-!
# O-CH11-SKEL (G1)：A12 `exists_surgery_with_decaying_accuracy` 的显式供给

A12 的结论是 `∃ δ F, AntitoneOn δ (Ici 0) ∧ hdec ∧ hasAnalyticAdmissibility F δ`。这里把它拆成
对**同一组数据** `(F, q, records, ε, C1, C2, κ, α)` 的命名供给（每个都是对树内已有类型的
`Prop`），按选择顺序：先 flow `F` 与 `q : CutoffParameters`、records，再常数 `ε C1 C2`、`κ`，
最后 larger-ball accuracy `α`。δ 取 `q.delta`（`accuracy_eq := rfl`）。

供给（bundle `SurgerySupplies_C11S` 的九个合取项，与 profile 字段逐一对应）：
* S1 `AccuracyDecaySupply_C11S q.delta`：A12 的两个 δ 条款；
* S2 `RadiusAntitoneSupply_C11S q`：`radius_antitone`；
* S3 `CanonicalWindowsSupply_C11S records`：`canonical_windows`；
* S4 `CanonicalConstantsSupply_C11S ε C1 C2`：`epsilon_pos / epsilon_small / C1_ge_one / C2_ge_one`；
* S5 `CanonicalSupply_C11S F q.neckRadius ε C1 C2`：`canonical`；
* S6 `NoncollapseSupply_C11S F κ ε`：`kappa_pos / kappa_antitone / noncollapsed`；
* S7 `LargerBallAccuracySupply_C11S q.delta α`：`largerBallAccuracy` 的三律 + `diagonal_smallness`；
* S8 `LargerBallScalarLargeSupply_C11S F q.delta α`：`larger_ball_scalar_control` 的 **A > 1**
  部分（KL 84.1(c)，DIGEST 的 `hLB`；astra 唯一 "Missing physical implication"）；
* S9 `RecentCutoffSupply_C11S records`：`recent_cutoff_smallness`。

树内已证、**不进 bundle** 的字段：`pinching` + `scalar_lower`（`curvatureLower_of_records_C11S`，
只用 records 的 preservation 与 slab barrier）、`larger_ball_scalar_control` 的 `0 < A ≤ 1`
（`largerBallScalarAt_of_le_one_C11S`，rbar = 1，K = 3）。另给上游 discharge 的树内适配：
`accuracyDecaySupply_of_tendsto_C11S`（`Tendsto δ atTop (𝓝 0)` 形）、
`largerBallAccuracySupply_diagonal_C11S`（α = `2 δ(max 0 (A/4))`）、
`recentCutoffSupply_of_recentScale_C11S` 与 `recentScaleSupply_of_doubling_C11S`（S9 降为参数级）、
`canonicalSupply_of_history_C11S`（history 形 ⇒ postMetric 形）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 数据：同一 flow 上的 records -/

/-- 同一 flow `F` 的每个 history `n`、每个 event `i` 上、参数为 `q` 的 cutoff record（数据）。 -/
abbrev CutoffRecords_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) :=
  ∀ n (i : Fin (F.tower.history n).eventCount),
    GeometricCutoffRecord (F.tower.history n).toHistory i q

/-! ## S1：δ 条款 -/

/-- **S1**：A12 结论里 δ 的两个条款（antitone 与 decay），逐字。 -/
def AccuracyDecaySupply_C11S (δ : ℝ → ℝ) : Prop :=
  AntitoneOn δ (Ici 0) ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε

/-- S1 的树内适配：astra 的 tuple 输出 `Tendsto q.delta atTop (𝓝 0)`，这里转成 A12 的 decay 形。 -/
theorem accuracyDecaySupply_of_tendsto_C11S {δ : ℝ → ℝ} (hanti : AntitoneOn δ (Ici 0))
    (hlim : Tendsto δ atTop (𝓝 0)) : AccuracyDecaySupply_C11S δ := by
  refine ⟨hanti, fun ε hε => ?_⟩
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hlim ε hε
  refine ⟨B, fun t ht => ?_⟩
  have hd := hB t ht.le
  rw [Real.dist_eq, sub_zero] at hd
  exact (le_abs_self _).trans_lt hd

/-! ## S2–S4：参数与常数 -/

/-- **S2**：`radius_antitone`。 -/
def RadiusAntitoneSupply_C11S (q : CutoffParameters) : Prop :=
  AntitoneOn q.neckRadius (Ici 0)

/-- **S3**：`canonical_windows`（selected records 的每个 static witness 有 canonical window）。 -/
def CanonicalWindowsSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) : Prop :=
  ∀ n i b, ((records n i).static b).hasCanonicalWindow

/-- **S4**：canonical 常数 `0 < ε < 1/100`、`1 ≤ C1`、`1 ≤ C2`（在一切时间与 history 之前选定）。 -/
def CanonicalConstantsSupply_C11S (ε C1 C2 : ℝ) : Prop :=
  0 < ε ∧ ε < 1 / 100 ∧ 1 ≤ C1 ∧ 1 ≤ C2

/-! ## S5：canonical（postMetric 形与 history 形） -/

/-- **S5**：`canonical` 字段，阈值 `ρ(t)⁻²`（用时 `ρ := q.neckRadius`）。 -/
def CanonicalSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
    (ρ t ^ 2)⁻¹ < metricScalarAt (postMetric F.observation t) x →
    ∃ W : SpatialCanonicalWitness (postMetric F.observation t) ε C1 C2 x,
      W.capTubeHasNeckChart ε

/-- S5 的 history 形（astra tuple `exists_surgery_with_spatial_control_and_decay` 的输出形）。 -/
def HistoryCanonicalSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
    (ρ t ^ 2)⁻¹ < metricScalarAt
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) x →
    ∃ W : SpatialCanonicalWitness
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
      W.capTubeHasNeckChart ε

/-- 树内适配：history 形 ⇒ postMetric 形（在 `n = ⌈t⌉` 的 history 上读 `postMetric`）。 -/
theorem canonicalSupply_of_history_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ)
    (h : HistoryCanonicalSupply_C11S F ρ ε C1 C2) : CanonicalSupply_C11S F ρ ε C1 C2 := by
  intro t ht x hx
  let n := Nat.ceil (max t 0)
  let H := (F.tower.history n).toHistory
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨max t 0, le_max_right t 0, by
      change max t 0 ≤ (F.tower.history n).horizon
      rw [F.tower.horizon_eq]
      exact Nat.le_ceil (max t 0)⟩
  have hdomain : max t 0 ∈ (H.restrict b).stageDomain
      (Fin.last (H.restrict b).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨H.activeStage_time_le b, le_rfl⟩
  have hmetric : postMetric F.observation t =
      H.stageMetric (H.activeStage b) (max t 0) :=
    eq_of_heq (H.restrict_stageMetric b (Fin.last (H.restrict b).eventCount)
      (max t 0) hdomain)
  rw [hmetric] at hx ⊢
  have hρ : ρ (max t 0) = ρ t := by rw [max_eq_left ht]
  apply h n b x
  change (ρ (max t 0) ^ 2)⁻¹ < _
  rw [hρ]
  exact hx

/-! ## S6：noncollapse -/

/-- **S6**：`kappa_pos`、`kappa_antitone`、`noncollapsed`（κ 在 `n` 处取值）。 -/
def NoncollapseSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (κ : ℝ → ℝ) (ε : ℝ) : Prop :=
  (∀ t, 0 ≤ t → 0 < κ t) ∧ AntitoneOn κ (Ici 0) ∧
    ∀ n, (F.tower.history n).NoncollapsedBefore (κ n) ε n

/-! ## S7：larger-ball accuracy 的数值律 -/

/-- **S7**：`largerBallAccuracy_pos`、两个 antitone 律、`diagonal_smallness`。 -/
def LargerBallAccuracySupply_C11S (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) : Prop :=
  (∀ A t, 0 < A → 0 ≤ t → 0 < α A t) ∧
    (∀ A, 0 < A → AntitoneOn (α A) (Ici 0)) ∧
    (∀ t, 0 ≤ t → AntitoneOn (fun A => α A t) (Ioi 0)) ∧
    ∀ t, 0 < t → δ t < α (2 * t) (2 * t)

/-- 对角 accuracy `α(A, t) = 2 δ(max 0 (A/4))`（与 astra `diagonalLargerBallAccuracy` 同形）。 -/
def diagonalAccuracy_C11S (δ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun A _ => 2 * δ (max 0 (A / 4))

/-- 树内：δ antitone 时对角 α 满足 S7 的全部数值律。 -/
theorem largerBallAccuracySupply_diagonal_C11S (q : CutoffParameters)
    (hanti : AntitoneOn q.delta (Ici 0)) :
    LargerBallAccuracySupply_C11S q.delta (diagonalAccuracy_C11S q.delta) := by
  refine ⟨fun A t _ _ => ?_, fun A _ => ?_, fun t _ => ?_, fun t ht => ?_⟩
  · have := q.delta_pos (max 0 (A / 4)) (le_max_left _ _)
    change 0 < 2 * q.delta (max 0 (A / 4))
    linarith
  · intro s _ s' _ _
    exact le_rfl
  · intro A _ A' _ hAA'
    change 2 * q.delta (max 0 (A' / 4)) ≤ 2 * q.delta (max 0 (A / 4))
    have hm : max 0 (A / 4) ≤ max 0 (A' / 4) :=
      max_le_max le_rfl (by linarith)
    have := hanti (mem_Ici.2 (le_max_left 0 (A / 4))) (mem_Ici.2 (le_max_left 0 (A' / 4))) hm
    linarith
  · change q.delta t < 2 * q.delta (max 0 (2 * t / 4))
    have hmax : max 0 (2 * t / 4) = t / 2 := by
      rw [max_eq_right (by linarith)]
      ring
    rw [hmax]
    have hpos := q.delta_pos (t / 2) (by linarith)
    have hle := hanti (show t / 2 ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith)
      (show t ∈ Ici (0 : ℝ) from ht.le) (by linarith)
    linarith

/-! ## S8：larger-ball scalar control（A ≤ 1 树内，A > 1 供给） -/

/-- `larger_ball_scalar_control` 在一个放大因子 `A` 处的陈述（字段体逐字）。 -/
def LargerBallScalarAt_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (A : ℝ) : Prop :=
  ∃ rbar K : ℝ, 0 < rbar ∧ 0 < K ∧
    ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
      2 * r ^ 2 < (t : ℝ) →
      (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
      hasSmallParabolicCurvature H t p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      r ≤ rbar * Real.sqrt t →
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ K * (r ^ 2)⁻¹

/-- **S8**（`hLB`）：`larger_ball_scalar_control` 的 `A > 1` 部分 = KL 84.1(c)。 -/
def LargerBallScalarLargeSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) : Prop :=
  ∀ A, 1 < A → LargerBallScalarAt_C11S F δ α A

/-- 树内：小抛物曲率 ⇒ `B(p, r)` 上 `|R| ≤ 3 r⁻²`（终端时刻读 trace 的 `|Rm|` 界）。 -/
theorem hasSmallParabolicCurvature_scalar_abs_le_C11S
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r : ℝ}
    (h : hasSmallParabolicCurvature H t p r)
    {q : (H.stageAt t).Carrier}
    (hq : q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) :
    |metricScalarAt (H.stageMetric (H.activeStage t) t) q| ≤ 3 * (r ^ 2)⁻¹ := by
  obtain ⟨hr, a, hat, _, htrace⟩ := h
  obtain ⟨B, hB⟩ := htrace q hq
  have hbound := hB.1 t hat le_rfl
  rw [B.endpoint_eq] at hbound
  have hscalar := sq_mul_scalar_abs_le_of_rm_bound
    (H.stageMetric (H.activeStage t) t) q hbound
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hscalar
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hscalar
  norm_num at hscalar
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

/-- 树内：`A ≤ 1` 时 `larger_ball_scalar_control` 的字段体成立（rbar = 1，K = 3；任意 F、δ、α）。 -/
theorem largerBallScalarAt_of_le_one_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) {A : ℝ}
    (hA1 : A ≤ 1) : LargerBallScalarAt_C11S F δ α A := by
  refine ⟨1, 3, one_pos, by norm_num, ?_⟩
  intro n H t p r _ _ hsmall _ _ q hq
  have hr : 0 < r := hsmall.1
  have hAr : A * r ≤ r := by nlinarith
  have hq' := riemannianBallOf_mono _ p hAr hq
  exact (le_abs_self _).trans (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hq')

/-- 树内：S8（A > 1）⇒ 整个 `larger_ball_scalar_control`。 -/
theorem largerBallScalar_of_large_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (hLB : LargerBallScalarLargeSupply_C11S F δ α) :
    ∀ A, 0 < A → LargerBallScalarAt_C11S F δ α A := by
  intro A _
  rcases le_or_gt A 1 with hA1 | hA1
  · exact largerBallScalarAt_of_le_one_C11S F δ α hA1
  · exact hLB A hA1

/-! ## S9：recent cutoff smallness -/

/-- **S9**：`recent_cutoff_smallness`（字段体逐字）。 -/
def RecentCutoffSupply_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
    ∀ t, T ≤ t → ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
      ∀ h, (records n i).nominalRadius h ≤ ε * q.neckRadius t

/-- S9 的参数级替代：晚期 `δ(u)² ρ(u) ≤ ε ρ(t)`（`u ∈ [t/2, t]`），只涉及 `q`。 -/
def RecentScaleSupply_C11S (q : CutoffParameters) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ u ∈ Icc (t / 2) t,
    q.delta u ^ 2 * q.neckRadius u ≤ ε * q.neckRadius t

/-- 半时倍增界：晚期 `ρ(u) ≤ C ρ(t)`（`u ∈ [t/2, t]`）。 -/
def RadiusDoublingSupply_C11S (q : CutoffParameters) : Prop :=
  ∃ C T₀ : ℝ, 0 < C ∧ ∀ t, T₀ ≤ t → ∀ u ∈ Icc (t / 2) t, q.neckRadius u ≤ C * q.neckRadius t

/-- 树内：参数级 S9′ ⇒ S9（用 record 的 `nominal_small : nominal < δ(u)² ρ(u)`）。 -/
theorem recentCutoffSupply_of_recentScale_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (h : RecentScaleSupply_C11S q) :
    RecentCutoffSupply_C11S records := by
  intro ε hε
  obtain ⟨T, hT, hscale⟩ := h ε hε
  refine ⟨T, hT, fun t ht n i hi h' => ?_⟩
  exact ((records n i).nominal_small h').le.trans (hscale t ht _ hi)

/-- 树内：δ decay + 半时倍增 ⇒ S9′。 -/
theorem recentScaleSupply_of_doubling_C11S (q : CutoffParameters)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → q.delta t < ε)
    (hdbl : RadiusDoublingSupply_C11S q) : RecentScaleSupply_C11S q := by
  obtain ⟨C, T₀, hC, hdbl⟩ := hdbl
  intro ε hε
  obtain ⟨B, hB⟩ := hdec (min 1 (ε / C)) (lt_min one_pos (div_pos hε hC))
  refine ⟨max T₀ (2 * |B| + 2), lt_max_of_lt_right (by positivity), fun t ht u hu => ?_⟩
  have hB0 := abs_nonneg B
  have hBB := le_abs_self B
  have ht0 : 2 * |B| + 2 ≤ t := (le_max_right _ _).trans ht
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hδ : q.delta u < ε / C := (hB u (by linarith [hu.1])).trans_le (min_le_right _ _)
  have hδpos := q.delta_pos u hu0
  have hδ1 := q.delta_lt_one u hu0
  have hru := q.neckRadius_pos u hu0
  have hrt := q.neckRadius_pos t (by linarith)
  have hd := hdbl t ((le_max_left _ _).trans ht) u hu
  have hsq : q.delta u ^ 2 ≤ q.delta u := by nlinarith
  calc q.delta u ^ 2 * q.neckRadius u ≤ q.delta u * q.neckRadius u :=
        mul_le_mul_of_nonneg_right hsq hru.le
    _ ≤ q.delta u * (C * q.neckRadius t) := mul_le_mul_of_nonneg_left hd hδpos.le
    _ ≤ ε / C * (C * q.neckRadius t) :=
        mul_le_mul_of_nonneg_right hδ.le (by positivity)
    _ = ε * q.neckRadius t := by field_simp

/-! ## 树内：pinching 与 scalar lower（只用 records） -/

private theorem stageMetric_scalarLower_C11S
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c : ℝ} (hc : 0 < c)
    (hzero : ∀ x : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) x)
    (j : Fin (H.eventCount + 1)) {t : ℝ} (ht : t ∈ H.stageDomain j)
    (x : (H.stage j).Carrier) :
    -3 / (2 * (t + c)) ≤ metricScalarAt (H.stageMetric j t) x := by
  have hstage := stageInitial_scalarLowerBound_of_history records hc hzero
  cases j using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at ht
    by_cases hfin : H.time (Fin.last H.eventCount) < H.horizon
    · have hmetric : H.stageMetric (Fin.last H.eventCount) t =
          (H.finalSlab hfin).flow.base.metric t := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hfin]
      rw [hmetric]
      exact closedSlab_scalarLowerBarrier_le hfin (H.time_nonneg _) hc (H.finalSlab hfin)
        (fun z => by rw [H.final_initial hfin]; exact hstage _ z) ht x
    · have ht' : t = H.time (Fin.last H.eventCount) :=
        le_antisymm (ht.2.trans (le_of_not_gt hfin)) ht.1
      have hmetric : H.stageMetric (Fin.last H.eventCount) t =
          H.initialMetric (Fin.last H.eventCount) := by
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_right hfin]
      rw [hmetric, ht']
      exact hstage _ x
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at ht
    have hmetric : H.stageMetric i.castSucc t = (H.event i).incoming.flow.base.metric t := by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rw [hmetric]
    exact incomingSlab_scalarLowerBarrier_le (H.time_nonneg _) hc (H.event i).incoming
      (fun z => by rw [H.event_initial i]; exact hstage _ z) ht x

/-- 树内：只要同一 flow 上有 records，就有 `a > 0` 使 postMetric 满足 `pinching`（shift `a`）与
`scalar_lower`（shift `a/2`）。初始 `a` 由紧性取（`exists_pos_inFixedHamiltonIveyRegion_…`）。 -/
theorem curvatureLower_of_records_C11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 ≤ t → ∀ x : (postStage F.observation t).Carrier,
      InFixedHamiltonIveyRegion (postMetric F.observation t) (a + t) x ∧
        -3 / (2 * (t + a / 2)) ≤ metricScalarAt (postMetric F.observation t) x := by
  obtain ⟨a, ha, hfixed, hscalar⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨a, ha, ?_⟩
  intro t ht x
  let n := Nat.ceil (max t 0)
  let H := (F.tower.history n).toHistory
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨max t 0, le_max_right t 0, by
      change max t 0 ≤ (F.tower.history n).horizon
      rw [F.tower.horizon_eq]
      exact Nat.le_ceil (max t 0)⟩
  have hzero := (F.tower.initial n).fixedHamiltonIveyRegion_and_scalar_lower_bound
    hfixed hscalar
  have hpinching := H.fixedHamiltonIveyRegion_and_scalar_lower
    (records n) ha hzero.1 hzero.2
  have hscalarZero : ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + a / 2)) ≤ metricScalarAt (H.initialMetric 0) y := by
    intro y
    simpa only [H.time_zero, zero_add, show 2 * (a / 2) = a by ring] using hzero.2 y
  have hdomain : max t 0 ∈ (H.restrict b).stageDomain
      (Fin.last (H.restrict b).eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last, Set.mem_Icc]
    exact ⟨H.activeStage_time_le b, le_rfl⟩
  have hmetric : postMetric F.observation t =
      H.stageMetric (H.activeStage b) (max t 0) :=
    eq_of_heq (H.restrict_stageMetric b (Fin.last (H.restrict b).eventCount)
      (max t 0) hdomain)
  have hpin := (hpinching.1 (H.activeStage b) (max t 0) (H.activeStage_mem b) x).1
  have hsc := stageMetric_scalarLower_C11S H (records n)
    (half_pos ha) hscalarZero (H.activeStage b) (t := max t 0) (H.activeStage_mem b) x
  rw [hmetric]
  constructor
  · have hparameter : a + t = a + max t 0 := by rw [max_eq_left ht]
    rw [hparameter]
    exact hpin
  · have hparameter : -3 / (2 * (t + a / 2)) =
        -3 / (2 * (max t 0 + a / 2)) := by rw [max_eq_left ht]
    rw [hparameter]
    exact hsc

/-! ## bundle -/

/-- **A12 的供给 bundle**：同一组数据上 S1–S9 同时成立。数据按选择顺序存在量化；
`pinching / scalar_lower` 与 `larger_ball_scalar_control`（`A ≤ 1`）不在其中（树内已证）。 -/
def SurgerySupplies_C11S (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ),
    AccuracyDecaySupply_C11S q.delta ∧ RadiusAntitoneSupply_C11S q ∧
    CanonicalWindowsSupply_C11S records ∧ CanonicalConstantsSupply_C11S ε C1 C2 ∧
    CanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧ NoncollapseSupply_C11S F κ ε ∧
    LargerBallAccuracySupply_C11S q.delta α ∧ LargerBallScalarLargeSupply_C11S F q.delta α ∧
    RecentCutoffSupply_C11S records

end GC.LongTime.Ch11
