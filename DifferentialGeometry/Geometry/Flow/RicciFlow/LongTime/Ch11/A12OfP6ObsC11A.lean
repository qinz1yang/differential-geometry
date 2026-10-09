import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfP6C11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.AccuracyDecayC11RA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RadiusAntitoneC11RA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CanonicalWindowsSupplyC11RB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RecentCutoffSupplyC11RC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryCanonicalSupplyC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.NoncollapseProfileC11RO

set_option autoImplicit false

/-!
# O-CH11-ASM (G4)：对接五个重证 helper——W1 归约到观察层逐层事实

astra 的 narrow tuple 由 `PreparedSpatialChain.exists_surgery_with_spatial_control`
（ch11src `SH/PreparedSpatialSurgery.lean:23`）从**观察层**数据得到：第 `n` 个观察 history
`F.tower.history n`、它的参数 `p n`、records `old n`（参数 `p n`），q 取 `diagonal p`。
这里在树内把 G3 的 `hflow`（W1 ∧ S8）从观察层数据推出（`hflow_of_obs_C11A`），用到：
* S1 `diagonal_delta_antitone_C11RA` + `accuracyDecaySupply_of_small_values_C11RA`（REPROVE-A），
  再用 `tendsto_of_accuracyDecaySupply_C11RA` 得 W1 的 `Tendsto`；
* S2 `radiusAntitoneSupply_diagonal_C11RA`（REPROVE-A）；
* S3 `canonicalWindowsSupply_of_diagonal_C11RB`，records := `diagonalRecords_C11RB`（REPROVE-B）；
* S5 `historyCanonicalSupply_of_diagonal_C11RD`（REPROVE-D）；
* S6 `noncollapseSupply_of_levels_C11RO`（REPROVE-O，κ 由 common profile 给）；
* S9 `recentCutoffSupply_of_accuracy_C11RC`（REPROVE-C 参数级入口），比较式由逐层的
  `hscale` 经 prefix 相容性搬到 `diagonal p`（本文件 `diagonal_scale_C11A`）；
* `htime`（事件时间 ≤ n）树内：`time_le_horizon_at` + `horizon_eq`。

剩下的前提全是**逐层观察事实**（astra `ScaffoldState` / `observation n` 的字段 + 参数链的数值性质）
与 S8；它们由 outer tuple 的递归构造给出（未分配，见 design §5）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

universe u

/-- 观察 history `n` 的事件时间 ≤ `n`（`diagonalRecords_C11RB` 的 `htime`，树内）。 -/
theorem tower_time_le_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (n : ℕ) (i : Fin (F.tower.history n).eventCount) :
    (F.tower.history n).toHistory.time i.succ ≤ (n : ℝ) := by
  have h := (F.tower.history n).toHistory.time_le_horizon_at i.succ
  change _ ≤ (F.tower.history n).horizon at h
  rw [F.tower.horizon_eq] at h
  exact h

/-- 逐层比较式 `δ(u)²ρ(u) < ρ(2u)/(u+1)`（`2u ≤ n`）经 prefix 相容性 ⇒ `diagonal p` 上的比较式
（`recentCutoffSupply_of_accuracy_C11RC` 的 `haccuracy`）。 -/
theorem diagonal_scale_C11A (p : ℕ → CutoffParameters)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (hscale : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → 2 * u ≤ (n : ℝ) →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (u + 1)) :
    ∀ u : ℝ, 0 ≤ u → (CutoffParameters.diagonal p).delta u ^ 2 *
      (CutoffParameters.diagonal p).neckRadius u <
        (CutoffParameters.diagonal p).neckRadius (2 * u) / (u + 1) := by
  intro u hu
  have h2u : 2 * u ≤ (Nat.ceil (2 * u) : ℝ) := Nat.le_ceil _
  have hu' := CutoffParameters.diagonal_eq_on_prefix p hcompat (Nat.ceil (2 * u))
    (show u ∈ Icc (0 : ℝ) (Nat.ceil (2 * u) : ℝ) from ⟨hu, by linarith⟩)
  have h2u' := CutoffParameters.diagonal_eq_on_prefix p hcompat (Nat.ceil (2 * u))
    (show 2 * u ∈ Icc (0 : ℝ) (Nat.ceil (2 * u) : ℝ) from ⟨by linarith, h2u⟩)
  rw [hu'.1, hu'.2.1, h2u'.2.1]
  exact hscale _ u hu h2u

/-- **观察层 ⇒ G3 的 `hflow`（W1 ∧ S8）**：q := `diagonal p`，records := `diagonalRecords_C11RB`，
κ 由逐层 κ 的 common profile 给出。前提只有逐层观察事实与 S8。 -/
theorem hflow_of_obs_C11A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (ε C1 C2 : ℝ) (κ : ℕ → ℝ)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (hδanti : ∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ)))
    (hρanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ)))
    (hδsmall : ∀ η : ℝ, 0 < η → ∃ n : ℕ, (p n).delta n < η)
    (hscale : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → 2 * u ≤ (n : ℝ) →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (u + 1))
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow)
    (hobs : ∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hlev : ∀ n : ℕ, 0 < κ n ∧ (F.tower.history n).NoncollapsedBefore (κ n) ε n)
    (hP6 : LargerBallScalarLargeSupply_C11S F (CutoffParameters.diagonal p).delta
      (diagonalAccuracy_C11S (CutoffParameters.diagonal p).delta)) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) := by
  let q := CutoffParameters.diagonal p
  let records := diagonalRecords_C11RB F p old hstatic hcompat (tower_time_le_C11A F)
  have hqanti : AntitoneOn q.delta (Ici 0) :=
    diagonal_delta_antitone_C11RA p (fun m k hmk t ht => (hcompat m k hmk t ht).1) hδanti
  have hS1 : AccuracyDecaySupply_C11S q.delta := by
    refine accuracyDecaySupply_of_small_values_C11RA hqanti fun η hη => ?_
    obtain ⟨n, hn⟩ := hδsmall η hη
    refine ⟨n, Nat.cast_nonneg n, ?_⟩
    change (p (Nat.ceil (n : ℝ))).delta n < η
    rw [Nat.ceil_natCast]
    exact hn
  have hS2 : RadiusAntitoneSupply_C11S q :=
    radiusAntitoneSupply_diagonal_C11RA p (fun m k hmk t ht => (hcompat m k hmk t ht).2.1)
      hρanti
  obtain ⟨κ', -, hκpos, hκanti, hnc⟩ := noncollapseSupply_of_levels_C11RO F κ ε hlev
  refine ⟨F, q, κ', records, ε, C1, C2, hconst, hκpos, hκanti, hqanti, hS2,
    historyCanonicalSupply_of_diagonal_C11RD F p hcompat hobs,
    canonicalWindowsSupply_of_diagonal_C11RB F p old hwin hstatic hcompat
      (tower_time_le_C11A F), hnc,
    tendsto_of_accuracyDecaySupply_C11RA (fun t ht => q.delta_pos t ht) hS1,
    recentCutoffSupply_of_accuracy_C11RC records hS2 (diagonal_scale_C11A p hcompat hscale),
    hP6⟩

/-- **A12 ⇐ 观察层逐层事实 + S8**（G4 主定理）：结论与 A12 逐字相同。 -/
theorem exists_surgery_with_decaying_accuracy_of_P6_obs_C11A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (ε C1 C2 : ℝ) (κ : ℕ → ℝ)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (hδanti : ∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ)))
    (hρanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ)))
    (hδsmall : ∀ η : ℝ, 0 < η → ∃ n : ℕ, (p n).delta n < η)
    (hscale : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → 2 * u ≤ (n : ℝ) →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (u + 1))
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow)
    (hobs : ∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hlev : ∀ n : ℕ, 0 < κ n ∧ (F.tower.history n).NoncollapsedBefore (κ n) ε n)
    (hP6 : LargerBallScalarLargeSupply_C11S F (CutoffParameters.diagonal p).delta
      (diagonalAccuracy_C11S (CutoffParameters.diagonal p).delta)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_P6_C11A P g
    (hflow_of_obs_C11A F p old ε C1 C2 κ hconst hstatic hcompat hδanti hρanti hδsmall hscale
      hwin hobs hlev hP6)

/-- 逐字对齐：G4 主定理的结论类型就是 A12 的类型。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (ε C1 C2 : ℝ) (κ : ℕ → ℝ)
    (hconst : CanonicalConstantsSupply_C11S ε C1 C2)
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (hδanti : ∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ)))
    (hρanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ)))
    (hδsmall : ∀ η : ℝ, 0 < η → ∃ n : ℕ, (p n).delta n < η)
    (hscale : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → 2 * u ≤ (n : ℝ) →
      (p n).delta u ^ 2 * (p n).neckRadius u < (p n).neckRadius (2 * u) / (u + 1))
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow)
    (hobs : ∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      ((p n).neckRadius t ^ 2)⁻¹ < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hlev : ∀ n : ℕ, 0 < κ n ∧ (F.tower.history n).NoncollapsedBefore (κ n) ε n)
    (hP6 : LargerBallScalarLargeSupply_C11S F (CutoffParameters.diagonal p).delta
      (diagonalAccuracy_C11S (CutoffParameters.diagonal p).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  exists_surgery_with_decaying_accuracy_of_P6_obs_C11A F p old ε C1 C2 κ hconst hstatic hcompat
    hδanti hρanti hδsmall hscale hwin hobs hlev hP6

end GC.LongTime.Ch11
