import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceScalarControl_P6L

/-!
# L6-A spine 1(b)：`BackwardTraceDistortionTerminal:58` 的 footprint 局部化（`_P6L`）

原 private `RetainedCoreHistory.normSq_stageMetric_le_of_backwardPointTrace_of_final`
（`ST/BackwardTraceDistortionTerminal.lean:58`）的导数界前提 `hslabs : EventSlabsDerivative`、
`hcurrent`/`hfinal : DerivativeBoundBefore`（carrier 全局）只经 `BTSC:168` 用 [V]；改调 P6A2 G6 的
`scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L`，前提照它写成 footprint 形：
`hslabs` 在 trace `A` 的点 `A.point i.castSucc …` 上、`hcurrent`/`hfinal` 在端点 `p` 上（`HEq y p`）。
pinching 全局不变。复制为 private `_P6L`（BTCC_P6L 以 `open private` 调用）；证明体照抄；结论逐字。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem normSq_stageMetric_le_of_backwardPointTrace_of_final_P6L
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : ∀ i : Fin H.toHistory.eventCount, ∀ hf : H.toHistory.activeStage u ≤ i.castSucc,
      ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ),
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t,
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t,
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
    normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L hut A hslabs
    hcurrent hfinal (by linarith) hqcan hscalar htime v huv hvt
  have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v
    (fun h => hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt)))
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt))
  have hmax : max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt))) 1 ≤ 2 * M := max_le hscal (by linarith)
  have h1 := hs.trans (mul_le_mul_of_nonneg_left hmax hC)
  have hN := normSq0S_nonneg (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt)) 4
    (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt)))
  rw [← Real.sq_sqrt hN]
  calc _ ≤ (4 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (2 * M)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
