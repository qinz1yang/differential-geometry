import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6EventClosedWindowIdentC12A

set_option autoImplicit false

/-!
# C12-5 consumer（`_C12A`）：通用识别 API 复原树内 survivor slab 的闭窗 Gram

`backwardSurvivorSlabMetric` 正是 `localPullMetric (terminal.extendedMetric v) terminalMap`；
用 `chartGramMatrix_closedWindow_extended_C12A`（`g := slab`、`ψ := backwardSurvivorTerminalMap`）
给出 `[c, time i.succ]`（`time i.castSucc ≤ c < time i.succ`）上的 chart Gram 联合光滑。
-/

noncomputable section

open Set Bundle Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

/-- consumer（`_C12A`）：survivor slab 在 `[c, time i.succ]` 上的闭窗 Gram 联合光滑。 -/
theorem survivorSlab_closedWindowGram_C12A (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) {c : ℝ} (hc : H.time i.castSucc ≤ c)
    (hcs : c < H.time i.succ)
    (x₀ : H.backwardSurvivorDomain first last hle) (j k : Fin (Module.finrank ℝ ThreeSpace)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × H.backwardSurvivorDomain first last hle =>
        Tensor.Coordinates.chartGramMatrix
          (H.backwardSurvivorSlabMetric first last hle i hf hl q.1) x₀ q.2 j k)
      (Icc c (H.time i.succ) ×ˢ
        (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) :=
  chartGramMatrix_closedWindow_extended_C12A (H.event i).terminal
    (H.backwardSurvivorTerminalMap first last hle i hf hl)
    (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hf hl)
    (H.backwardSurvivorSlabMetric first last hle i hf hl) hc hcs
    (fun v _ hv => by
      change localPullMetric _ _ _ = localPullMetric _ _ _
      rw [(H.event i).terminal.extendedMetric_before hv])
    (by
      change localPullMetric _ _ _ = localPullMetric _ _ _
      rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal])
    x₀ j k

end GC.LongTime.Ch11
