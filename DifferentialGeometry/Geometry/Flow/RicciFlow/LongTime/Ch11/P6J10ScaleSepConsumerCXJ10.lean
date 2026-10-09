import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10ScaleSepCXJ10

/-!
# CX-J10 G1 consumer（后缀 `_CXJ10`）

* `hOpenJ10_of_scaleSeparation_CXJ10`：P6WR `hOpen` 的 J10 合取**逐字形**（`Ho k := F.tower.history
  (ind k)`、`c k := r k ^ 2`、`hc k := pow_pos (hr k) 2`、`Qs n := qcanSup S (Ho n).horizon`）由
  `hJ10_of_scaleSeparation_CXJ10` 给出；前提只剩原尺度 scale separation `hsep`。
* `hOpenJ10_of_envelope_CXJ10`：同一逐字形，scale separation 以重标度 envelope 形
  `c n · qcanSup ≤ max (Qt n) (n+1)` 给出，`Qt k < R k`、`k + 1 < R k` 取自冻结 hgapJ 前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- hOpen 的 J10 合取（逐字 let 形）⇐ 原尺度 scale separation。 -/
theorem hOpenJ10_of_scaleSeparation_CXJ10 {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (σ : ∀ k, Icc (0 : ℝ)
      ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (pow_pos (hr k) 2)).toHistory.horizon)
    (y : ∀ k, (((F.tower.history (ind k)).rescale_P6N (r k ^ 2)
      (pow_pos (hr k) 2)).toHistory.stageAt (σ k)).Carrier) (R : ℕ → ℝ)
    (hRdef : ∀ k, R k = metricScalarAt (((F.tower.history (ind k)).rescale_P6N (r k ^ 2)
      (pow_pos (hr k) 2)).toHistory.stageMetric (((F.tower.history (ind k)).rescale_P6N (r k ^ 2)
        (pow_pos (hr k) 2)).toHistory.activeStage (σ k)) (σ k)) (y k))
    (hsep : ∀ n, GC.LongTime.Ch11.qcanSup_P6WR S (F.tower.history (ind n)).horizon <
      origScalar_CXJ10 (F.tower.history (ind n)) (pow_pos (hr n) 2) (σ n) (y n)) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let c : ℕ → ℝ := fun k => r k ^ 2
    let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
    ∀ n, c n * Qs n < R n :=
  hJ10_of_scaleSeparation_CXJ10 S (fun k => F.tower.history (ind k)) (fun k => r k ^ 2)
    (fun k => pow_pos (hr k) 2) σ y R hRdef hsep

/-- hOpen 的 J10 合取（逐字 let 形）⇐ 重标度 envelope 形 scale separation + 冻结前提。 -/
theorem hOpenJ10_of_envelope_CXJ10 {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (ind : ℕ → ℕ) (r R Qt : ℕ → ℝ) (hQt : ∀ k, Qt k < R k) (hR1 : ∀ k : ℕ, (k : ℝ) + 1 < R k)
    (henv : ∀ n, r n ^ 2 * GC.LongTime.Ch11.qcanSup_P6WR S (F.tower.history (ind n)).horizon ≤
      max (Qt n) ((n : ℝ) + 1)) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let c : ℕ → ℝ := fun k => r k ^ 2
    let Qs : ℕ → ℝ := fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon
    ∀ n, c n * Qs n < R n :=
  hJ10_of_envelope_CXJ10 hQt hR1 henv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
