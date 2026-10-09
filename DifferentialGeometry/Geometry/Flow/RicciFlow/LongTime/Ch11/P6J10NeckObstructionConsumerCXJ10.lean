import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10NeckObstructionCXJ10

/-!
# CX-J10 G2 consumer（后缀 `_CXJ10`）

`hOpenJ10_neckThreshold_false_CXJ10`：hOpen 帧（`Ho k := F.tower.history (ind k)`、`c k := r k ^ 2`、
`Tn k := rescaleTime Tno k`）+ 冻结 hgapJ 前提 `R k ≤ ((q.rescale_P6N (c k)).neckRadius (Tn k) ^ 2)⁻¹`
⇒ 若取 `Qs n := ρ((Ho n).horizon)⁻²`（`TimeDerivativeSupply_C11E` 的整条 history 阈值），J10 在每个
`n` 都不成立。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- hOpen 帧下 surgery 尺度阈值使 J10 处处失败。 -/
theorem hOpenJ10_neckThreshold_false_CXJ10 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (hρa : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (Tno : ∀ k, Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon) (R : ℕ → ℝ)
    (hQρ : ∀ k, R k ≤ ((q.rescale_P6N (r k ^ 2) (pow_pos (hr k) 2)).neckRadius
      ((F.tower.history (ind k)).rescaleTime_P6X (pow_pos (hr k) 2) (Tno k)) ^ 2)⁻¹) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    let c : ℕ → ℝ := fun k => r k ^ 2
    let Qs : ℕ → ℝ := fun n => (q.neckRadius (Ho n).horizon ^ 2)⁻¹
    ∀ n, ¬ c n * Qs n < R n :=
  fun n => not_hJ10_horizonNeck_CXJ10 q hρa (F.tower.history (ind n)) (pow_pos (hr n) 2) (Tno n)
    (hQρ n)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
