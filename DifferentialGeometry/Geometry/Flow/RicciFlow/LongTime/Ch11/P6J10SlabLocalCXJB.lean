import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10ScaleSepCXJ10

/-!
# J9/J10 的 slab 局部化（CX-J10B G1，后缀 `_CXJB`；路线 (B)）

D-8 裁定 2：J9 阈值取 `c·σ` 所在 slab 的 `qcan`，J10 = `c·Qs < R`。

**已证（PROVED，standard axioms）**：
* `eventSlabDerivative_qcanSup_single_CXJB`：**单 slab 版** —— slab `j` 的
  `DerivativeBoundBefore C.Ctime (qcanSup S (time j.succ)) (time j.succ)`；阈值只看到 slab 终点时刻
  （不看 `horizon`、不看后面的 slab）。
* `eventSlabsDerivative_qcanSup_upto_CXJB`：`k` 前缀版 `EventSlabsDerivative … (qcanSup S (time k)) k`；
  `k := Fin.last` 给出 **`qcanSup S (time last)`**（`≤ qcanSup S horizon`）这一最小的、冻结 slot
  `EventSlabsDerivative … (Fin.last _)` 能接受的 `qcanSup` 型阈值。
* `hJ9J10_of_slabLocal_CXJB`：`Qs n := qcanSup S (time last)` 重做 J9，J10 `c·Qs < R` ⟺ 原尺度
  `qcanSup S (time last) < R^orig`（CX-J10 `hJ10_iff_origSep_CXJ10` 的 `Θ := slab-local`）；
  旧 horizon 形 `hsep` ⇒ 新形（`hsepLoc_of_hsep_CXJB`）。
* `exists_Qs_slabLocal_CXJB`：jointD 形 `∃ Qs` 打包（J9 ∧ J10 ∧ KNOM Q 档 ∧ 两个 scale 合取）。

**BLOCKED（精确缺口，见 state-CX-J10B.md）**：新形 `hsepLoc`（`R^orig(cσ,y) > qcanSup S (time last)`）
仍不由冻结 hgapJ 前提给出。原因：冻结 J9 slot 的 `k` 是 `Fin.last`（全部 slab），而
`DerivativeBoundBefore` 的阈值必须 `≥` 每个 slab 所在带的 `qcan`（ch12 F2 `hQ`），故 `Qs` 不能只看 `σ`
所在 slab（该 slab 的 `j.succ ≤ last`）；且 `R^orig = R/c = R/r²` 与 `qcan` 的比较需要 `r`
相对 surgery 尺度的下界，hgapJ 无此前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace GC.LongTime.Ch11

open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`k` 前缀版**：slab `j < k` 的 derivative 阈值 `qcanSup S (time k)`。 -/
theorem eventSlabsDerivative_qcanSup_upto_CXJB {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ)
    (k : Fin ((F.tower.history n).eventCount + 1)) :
    (F.tower.history n).EventSlabsDerivative C.Ctime
      (qcanSup_P6WR S ((F.tower.history n).time k)) k := by
  have h := timeDerivativeSupply_of_astra_threshold_C12X S εcut Dcut mcut W hshift hoffset F
    hTower (qcanSup_P6WR S) (hQ_qcanSup_P6WR S)
  intro j hj y t ht hR
  have hjk : j.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hj
  have htk : t ≤ (F.tower.history n).time k :=
    ht.2.le.trans ((F.tower.history n).time_strictMono.monotone hjk)
  exact h.1 n j y t ht ((qcanSup_mono_P6WR S htk).trans_lt hR)

/-- **单 slab 版 `eventSlabsDerivative_qcanSup_P6WR`**：slab `j` 的 derivative 阈值
`qcanSup S (time j.succ)`（slab 终点时刻，不看 `horizon`）。 -/
theorem eventSlabDerivative_qcanSup_single_CXJB {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ)
    (j : Fin (F.tower.history n).eventCount) :
    ((F.tower.history n).toHistory.event j).incoming.DerivativeBoundBefore C.Ctime
      (qcanSup_P6WR S ((F.tower.history n).time j.succ)) ((F.tower.history n).time j.succ) :=
  eventSlabsDerivative_qcanSup_upto_CXJB S εcut Dcut mcut W hshift hoffset F hTower n j.succ j
    (Fin.castSucc_lt_succ)

/-- 末事件时刻处的阈值 `≤` horizon 处的阈值（`time last ≤ horizon`）。 -/
theorem qcanSup_time_last_le_CXJB {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (H : RetainedCoreHistory.{u}) :
    qcanSup_P6WR S (H.time (Fin.last H.eventCount)) ≤ qcanSup_P6WR S H.horizon :=
  qcanSup_mono_P6WR S H.time_le_horizon

/-- 旧 horizon 形 `hsep`（CX-J10）⇒ slab 局部形 `hsepLoc`。 -/
theorem hsepLoc_of_hsep_CXJB {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (Ho : ℕ → RetainedCoreHistory.{u}) {x : ℕ → ℝ}
    (hsep : ∀ n, qcanSup_P6WR S (Ho n).horizon < x n) :
    ∀ n, qcanSup_P6WR S ((Ho n).time (Fin.last (Ho n).eventCount)) < x n :=
  fun n => (qcanSup_time_last_le_CXJB S (Ho n)).trans_lt (hsep n)

/-- **`hJ9J10_of_slabLocal_CXJB`**：`Qs n := qcanSup S (time last)`：J9 无条件，J10 ⟺ `hsepLoc`。
结论 = J9 ∧ J10 ∧ `Qs n ≤ qcanSup S horizon`（不大于旧 `Qs`，故 J7 型 `Qs` 上界仍成立）。 -/
theorem hJ9J10_of_slabLocal_CXJB {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (ind : ℕ → ℕ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (σ : ∀ n, Icc (0 : ℝ) ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (y : ∀ n, (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.stageAt
      (σ n)).Carrier) (R : ℕ → ℝ)
    (hRdef : ∀ n, R n = metricScalarAt
      (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.stageMetric
      (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.activeStage (σ n)) (σ n))
      (y n))
    (hsepLoc : ∀ n, qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) <
      origScalar_CXJ10 (F.tower.history (ind n)) (hc n) (σ n) (y n)) :
    (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C.Ctime
      (qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount))) (Fin.last _)) ∧
    (∀ n, c n * qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) < R n) ∧
    (∀ n, qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) ≤
      qcanSup_P6WR S (F.tower.history (ind n)).horizon) :=
  ⟨fun n => eventSlabsDerivative_qcanSup_upto_CXJB S εcut Dcut mcut W hshift hoffset F hTower
      (ind n) (Fin.last _),
    (hJ10_iff_origSep_CXJ10 (fun n => F.tower.history (ind n)) hc σ y R hRdef).2 hsepLoc,
    fun n => qcanSup_time_last_le_CXJB S (F.tower.history (ind n))⟩

/-- **jointD 形 `∃ Qs` 打包（slab 局部）**：KNOM Q 档 `Qs ≤ Q` 及两个 scale 合取随 `Qs ≤ Q`。 -/
theorem exists_Qs_slabLocal_CXJB {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (ind : ℕ → ℕ)
    (c R Q Cb : ℕ → ℝ) {ι : ℕ → Type*} (scale : ∀ n, ι n → ℝ)
    (hJ : ∀ n, c n * qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) < R n)
    (hΘQ : ∀ n, qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) ≤ Q n)
    (hQa : ∀ (n : ℕ) b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Q n) ≤ scale n b)
    (hQb : ∀ n b, max (Q n) 1 ≤ Cb n * scale n b) :
    ∃ Qs : ℕ → ℝ, (∀ n, Qs n ≤ Q n) ∧
      (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C.Ctime (Qs n)
        (Fin.last (F.tower.history (ind n)).eventCount)) ∧
      (∀ n, c n * Qs n < R n) ∧
      (∀ (n : ℕ) b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤ scale n b) ∧
      (∀ n b, max (Qs n) 1 ≤ Cb n * scale n b) :=
  exists_Qs_slab_J10_CXJ10 (fun n => F.tower.history (ind n)) C.Ctime c _ R Q Cb scale
    (fun n => eventSlabsDerivative_qcanSup_upto_CXJB S εcut Dcut mcut W hshift hoffset F hTower
      (ind n) (Fin.last _)) hJ hΘQ hQa hQb

end GC.LongTime.Ch11
