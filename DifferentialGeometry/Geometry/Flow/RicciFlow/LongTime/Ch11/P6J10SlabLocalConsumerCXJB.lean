import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10SlabLocalCXJB

/-!
# CX-J10B G1 consumer：旧 horizon 形 `hsep`（CX-J10）喂 slab 局部 J9/J10 对（后缀 `_CXJB`）

`hJ9J10_of_horizonSep_CXJB`：CX-J10 的 `hsep`（`qcanSup S horizon < R^orig`）⇒ slab 局部
`Qs n := qcanSup S (time last)` 的 J9 ∧ J10（P6WR2 `hgapJ8` 的 `∃ Qs` 槽可用的一对）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature

namespace GC.LongTime.Ch11

open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem hJ9J10_of_horizonSep_CXJB {pBase : CutoffParameters}
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
    (hsep : ∀ n, qcanSup_P6WR S (F.tower.history (ind n)).horizon <
      origScalar_CXJ10 (F.tower.history (ind n)) (hc n) (σ n) (y n)) :
    (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C.Ctime
      (qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount))) (Fin.last _)) ∧
    (∀ n, c n * qcanSup_P6WR S ((F.tower.history (ind n)).time
        (Fin.last (F.tower.history (ind n)).eventCount)) < R n) :=
  let h := hJ9J10_of_slabLocal_CXJB S εcut Dcut mcut W hshift hoffset F hTower ind c hc σ y R hRdef
    (hsepLoc_of_hsep_CXJB S (fun n => F.tower.history (ind n)) hsep)
  ⟨h.1, h.2.1⟩

end GC.LongTime.Ch11
