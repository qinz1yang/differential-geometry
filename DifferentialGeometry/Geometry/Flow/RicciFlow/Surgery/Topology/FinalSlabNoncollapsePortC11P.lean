import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints

/-!
# S-CH11-FIX5 port of astra `FinalSlabNoncollapse`（`PortC11P`）

来源：donor `FinalSlabNoncollapse.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 5 个 `rw` / 类型不匹配 error（共 8 条消息），根因是同一个：`L := J.extendHorizon …` 的
`L.toHistory.eventCount` 与 `K.eventCount` 只是 defeq、不是 syntactically equal，所以
`rw [stageMetric_… ]` / `rw [hmetric]` 的 pattern（带 `Fin (L.toHistory.eventCount + 1)` 类型的
index）在 `rw` 的 reducible 匹配下找不到；另有一处 `hvt.trans t.2.2` 混用子类型序与实数序。
本 port 只做 elaboration 层面修补（no statement / definition / proof idea altered；`hmetric`
的陈述不变，证明思路仍是 "last / cast 两种 stage 分别化到 final slab / event incoming flow"）：
* `hmetric` 的 `last` / `cast` 两个分支：`rw [lemma, lemma]; rfl` 改为
  `refine (lemma (H := L.toHistory) …).trans ?_`，再
  `refine Eq.trans ?_ (lemma (H := K.toHistory) …).symm`，最后 `rfl`
  （用 `refine` 在默认透明度下统一 index，而不是 `rw` 的 syntactic 匹配）。
* `hxL`：`rw [hmetric]; exact hx` 改为先 `have hm : L…stageMetric (L…activeStage t) t = K…stageMetric
  (K…activeStage tK) tK := hmetric _ _`（由 `hmetric` 在默认透明度下实例化），再 `rw [hm]; exact hx`。
* `vL` 的 `⟨v, v.2.1, hvt.trans t.2.2⟩` 改为 `(show (v : ℝ) ≤ (t : ℝ) from hvt).trans t.2.2`
  （`hvt` 是子类型序，`t.2.2` 是实数序）。
* `hA.1` 分支的 `rw [hmetric] at hv; exact hv` 改为 `have hm`（以 `vL` / `v` 为参数，同上写法）
  再 `rw [hm] at hv; exact hv`。
* 末尾 `rw [hmetric]; exact hv` 同样改为 `have hm …; rw [hm]; exact hv`。

原路径 `FinalSlabNoncollapse` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- Noncollapse on an actual observed history controls each strict closed prefix
of its final smooth slab, with the same coefficient and radius ceiling. -/
theorem RetainedCoreHistory.terminalNoncollapsedBefore_finalSlab (K : RetainedCoreHistory.{u})
    (hfinal : K.time (Fin.last K.eventCount) < K.horizon)
    {κ ρ : ℝ} (hnc : K.NoncollapsedBefore κ ρ K.horizon) :
    let J := K.prefixAt (Fin.last K.eventCount)
    let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
    J.TerminalNoncollapsedBefore rfl G (K.final_initial hfinal) κ ρ K.horizon := by
  let J := K.prefixAt (Fin.last K.eventCount)
  let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
  change J.TerminalNoncollapsedBefore rfl G (K.final_initial hfinal) κ ρ K.horizon
  intro T hT hTK _
  let L := J.extendHorizon T hT.le (G.closedPrefix T hT hTK) (K.final_initial hfinal)
  change L.NoncollapsedBefore κ ρ T
  have hmetric (j : Fin (K.eventCount + 1)) (v : ℝ) :
      L.toHistory.stageMetric j v = K.toHistory.stageMetric j v := by
    cases j using Fin.lastCases with
    | last =>
      refine (ObservedHistory.stageMetric_last_of_lt (H := L.toHistory) (h := hT) v).trans ?_
      refine Eq.trans ?_
        (ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfinal) v).symm
      rfl
    | cast i =>
      refine (ObservedHistory.stageMetric_castSucc_apply (H := L.toHistory) i v).trans ?_
      refine Eq.trans ?_ (ObservedHistory.stageMetric_castSucc_apply (H := K.toHistory) i v).symm
      rfl
  intro t p r _ hr hball
  let tK : Icc (0 : ℝ) K.horizon := ⟨t, t.2.1, t.2.2.trans hTK.le⟩
  have hballK : K.toHistory.isParabolicallyRmControlledBall tK p r := by
    obtain ⟨hr0, a, hat, ha, htraces⟩ := hball
    let aK : Icc (0 : ℝ) K.horizon := ⟨a, a.2.1, a.2.2.trans hTK.le⟩
    refine ⟨hr0, aK, hat, ha, ?_⟩
    intro x hx
    have hxL : x ∈ riemannianBallOf
        (L.toHistory.stageMetric (L.toHistory.activeStage t) t) p r := by
      have hm : L.toHistory.stageMetric (L.toHistory.activeStage t) t =
          K.toHistory.stageMetric (K.toHistory.activeStage tK) tK := hmetric _ _
      rw [hm]
      exact hx
    obtain ⟨A, hA⟩ := htraces x hxL
    let B : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
        (K.toHistory.activeStage tK) (K.toHistory.activeStage_mono hat) x := {
      point := fun j hj hk => A.point j hj hk
      endpoint_eq := A.endpoint_eq
      crossing := fun i hi hl => A.crossing i hi hl }
    refine ⟨B, ?_, ?_⟩
    · intro v hav hvt
      let vL : Icc (0 : ℝ) L.horizon :=
        ⟨v, v.2.1, (show (v : ℝ) ≤ (t : ℝ) from hvt).trans t.2.2⟩
      have hv := hA.1 vL hav hvt
      have hm : L.toHistory.stageMetric (L.toHistory.activeStage vL) vL =
          K.toHistory.stageMetric (K.toHistory.activeStage v) v := hmetric _ _
      rw [hm] at hv
      exact hv
    · intro i hi hl
      exact hA.2 i hi hl
  have hv := hnc tK p r tK.2.2 hr hballK
  have hm : L.toHistory.stageMetric (L.toHistory.activeStage t) t =
      K.toHistory.stageMetric (K.toHistory.activeStage tK) tK := hmetric _ _
  rw [hm]
  exact hv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
