import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WideAtC11V4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.PresentedStaticCapRestrictionC11RB

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL4 G2：Q3 前提对齐 `hext` / profile 字段（`_C11V4`）

Q3 的四项前提（`hcan`、`hcapS`、`hdeg`、`nr ≤ M`）逐项从 `a12Enhanced_of_chain_C11P2` 的 `hext`
数据（= narrow tuple + P1/P3/hprof；它们正是 `EnhancedSurgeryProfile_C11E` 的
`linked_windows` / `collar_window` / `model_constraints` 与 `toAnalyticSurgeryProfile` 的
`radius_antitone` / `canonical_windows` / `canonical` 字段）给出：

* `nr ≤ M`：`AntitoneOn q.neckRadius (Ici 0)`（`radius_antitone`）⇒ `M = q.neckRadius 0`
  （THM，SMALLVOL3）。
* `hdeg`（`N`）：树内无条件（`exists_stageDegreeBound_C11V3`），`N` 依赖 `P`（THM）。
* `hcan`：`HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2` + 单调 + records 的 HI
  （THM，SMALLVOL3 G2）。
* `hcapS`：`LinkedWindowsSupply_C11E records`（P1）+ P3 collar 条 + hprof 的 `2 ≤ modelOrder`
  （THM，本文件，**D 限制**）。

**GAP-2 的新结论（本文件）**：`hcapS` 的静态帽用 `restrictCanonicalWindow_C11RB`（窗口半径 `D → 4·te+6`、
阶 `m → 2`、精度 `η → ε₀`）限制到固定参数 `(D₀ = 4·transitionEnd + 6, 2, ε₀)`，故
`ε₀ = ε₀(ε, C1, C2, N)` **不依赖 `q.modelRadius`**（SMALLVOL3 的版本里 `ε₀` 依赖 `D = q.modelRadius`，
与 `pBase.modelAccuracy` 一起选时有循环）。唯一残余的 `pBase` 约束 = `pBase.modelAccuracy ≤ ε₀(C.epsilon,
C1, C2, N(P))`，而 ch12 `PBaseC12X` 给的是 `pBase.modelAccuracy ≤ εProf`（`εReserve` 在 `∃ C` 之前，
不依赖 `N(P)`）——**不够**；精确修法（`εReserve := min εProf ε₀(…, N(P))`，在 `P g` 之后选）见
`docs/geometrization/chapter8/CH11-SMALLVOL-ALIGN-GAP2-OUTER-20261007.md` §5。
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

/-- **`hcapS`（D 限制版）**：records 的静态帽（`D = q.modelRadius`、`m = q.modelOrder`、
`η = q.modelAccuracy`）经 `restrictCanonicalWindow_C11RB` 限制到 `(D₀ = 4·te + 6, m = 2, η = ε₀)`，
canonical window 保持（`te < D₀ + 1`）。所以 G2 的 `ε₀` 只依赖 `(ε, C1, C2, N)`，不依赖 `q.modelRadius`。 -/
theorem hcapS_restrict_of_records_C11V4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (hwin : ∀ n i b, ((records n i).static b).hasCanonicalWindow) {ε₀ : ℝ}
    (hacc : q.modelAccuracy ≤ ε₀) (hord : 2 ≤ q.modelOrder)
    (hD : 4 * StandardCap.transitionEnd + 6 ≤ q.modelRadius) :
    ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        ∃ (fixed : StaticCapScaffold) (m : ℕ) (η : ℝ)
          (S : (H.event i).PresentedStaticCap fixed (4 * StandardCap.transitionEnd + 6) m η b),
          η ≤ ε₀ ∧ 2 ≤ m ∧ S.hasCanonicalWindow := by
  have hte := StandardCap.transitionEnd_pos
  have hD' : 0 < 4 * StandardCap.transitionEnd + 6 := by positivity
  intro n H i b
  exact ⟨q.fixed, 2, ε₀,
    ((records n i).static b).restrictCanonicalWindow_C11RB (hwin n i b) hD' hD hord hacc, le_rfl,
    le_rfl,
    ((records n i).static b).hasCanonicalWindow_restrictCanonicalWindow_C11RB (hwin n i b) hD' hD
      hord hacc (by linarith)⟩

/-- **Q3 入口（`hext` 形）**：`ε₀` 只依赖 `(ε, C1, C2, N)`。`hext` 的数据（`pBase` 的 P3 / hprof、
`q` 与 `pBase` 的参数等式、`records` 与 P1 `LinkedWindowsSupply_C11E`、`AntitoneOn q.delta`、
`AntitoneOn q.neckRadius`、`HistoryCanonicalSupply_C11S`）+ `N` + K 的 wide 供给（S7 取对角 `α`）
⇒ 每个 `A > 0` 的 `nr := 0` window。显式 binder：`pBase.modelAccuracy ≤ ε₀`（GAP-2）、`hdeg`
（`exists_stageDegreeBound_C11V3` 给出）、`LocalKappaWideSupply_C11Q`（GAP-3，归 KAPPA2）。 -/
theorem smallVolWindow_of_hext_C11V4 (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {pBase q : CutoffParameters} {A : ℝ}, 0 < A →
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.modelRadius = pBase.modelRadius → q.modelOrder = pBase.modelOrder →
      q.modelAccuracy = pBase.modelAccuracy → pBase.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      ∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'' := by
  obtain ⟨ε₀, hε₀, hE⟩ := localKappaWindow_zero_of_wide_window_late_C11V3.{u}
    (4 * StandardCap.transitionEnd + 6) le_rfl ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F pBase q A hA hP3 hprof hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hdeg
    hwide
  have hD : 4 * StandardCap.transitionEnd + 6 ≤ q.modelRadius := by
    rw [hrad]
    exact four_transitionEnd_le_modelRadius_C11V3 hP3
  have hord2 : 2 ≤ q.modelOrder := by
    rw [hord]
    exact hprof.2.1
  have hq : q.modelAccuracy ≤ ε₀ := by
    rw [hacc]
    exact hacc₀
  have hS7 := largerBallAccuracySupply_diagonal_C11S q hδanti
  obtain ⟨c, c', hc, hc', hHI, hlow⟩ := history_HI_and_lower_of_records_C11V3 records
  have hcomp := hcomp_late_of_HI_C11V3 (nr := q.neckRadius) (M := q.neckRadius 0)
    (q.neckRadius_pos 0 le_rfl) (fun s hs => hρanti (Set.mem_Ici.mpr le_rfl) hs hs) hc hc' hHI hlow
  obtain ⟨T₀, hcan⟩ := hcan_late_of_canonicalSupply_C11V3 hρanti hcanon hcomp
  obtain ⟨κ, hκ, hL⟩ := wideLate_of_wideSupply_C11V3 hS7
    (localKappaWideSupply_clamp_C11V3 hwide) hA
  exact hE (nr := fun s => q.neckRadius (max s 0)) (M := q.neckRadius 0) hA hκ
    (nr_clamp_le_C11V3 hρanti)
    (wideWindow_of_wideLate_C11V2 (F := F) (nr := fun s => q.neckRadius (max s 0)) (κ := κ) hA
      hL)
    (hcapS_restrict_of_records_C11V4 records (hwin_of_linkedWindows_C11V3 hlink) hq hord2 hD)
    ⟨T₀, by
      intro n H v v' hT0 hv'v w s hs hsnr hvs hcont
      have hmax : max (v : ℝ) 0 = v := max_eq_left v.2.1
      exact hcan n v v' hT0 hv'v w s hs (by simpa only [hmax] using hsnr) hvs hcont⟩
    hdeg

/-- consumer：`hext` 形入口 ⇒ `nr := 0` window ⇒ `tracedKappa_of_window_P6B`（M8 bridge）。 -/
example (ε C1 C2 : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {pBase q : CutoffParameters} {A : ℝ}, 0 < A →
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.modelRadius = pBase.modelRadius → q.modelOrder = pBase.modelOrder →
      q.modelAccuracy = pBase.modelAccuracy → pBase.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      (∀ n j, GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N) →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      True := by
  obtain ⟨ε₀, hε₀, hE⟩ := smallVolWindow_of_hext_C11V4.{u} ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F pBase q A hA hP3 hprof hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hdeg
    hwide
  obtain ⟨κ'', -, hW0⟩ := hE hA hP3 hprof hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon
    hdeg hwide
  have := tracedKappa_of_window_P6B hW0
  trivial

end GC.LongTime.Ch11
