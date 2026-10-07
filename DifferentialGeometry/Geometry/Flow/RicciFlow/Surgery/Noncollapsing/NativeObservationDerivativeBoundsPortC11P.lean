import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.PreparedObservationData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBirthGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric

/-!
# S-CH11-FIX8 port of astra `NativeObservationDerivativeBounds`（`PortC11P`）

来源：donor `NativeObservationDerivativeBounds.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（2 个 error）。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `time_derivative_gradient_on_stage` 末两个分支的
  `simp only [stageMetric_last_of_lt, stageMetric_castSucc_apply] at hscalar ⊢`：
  本树里 simp 进不了目标里 `show ℝ from mfderiv …`（`have` 体）里的
  `stageMetric`，只改写了一半，`exact onSlab …` 类型对不上。改为先证函数等式
  `K.toHistory.stageMetric _ = (…).flow.base.metric`（`funext` + 同一条引理），再
  `rw [hfun] at hscalar ⊢`。

原路径 `NativeObservationDerivativeBounds` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology
namespace GC.GeneralFlow
universe u

/-- The original native coefficients control interior time derivatives and the
actual slice gradient, including the birth metric of its outgoing slab. -/
theorem NativeEstimates.time_derivative_gradient_on_stage
    {K : RetainedCoreHistory.{u}}
    {ε C1 C2 C1s C2s qcan qs τmin : ℝ} {Ctime Cgrad : ℝ≥0}
    (hEst : NativeEstimates K ε C1 C2 C1s C2s qcan qs τmin Ctime Cgrad)
    (hqcan : 0 < qcan)
    (j : Fin (K.eventCount + 1)) (s : ℝ)
    (hs : s ∈ Ico (K.time j) (K.toHistory.stageEndTime j))
    (y : (K.stage j).Carrier)
    (hscalar : qcan < metricScalarAt (K.toHistory.stageMetric j s) y) :
    (K.time j < s →
      |derivWithin (fun v => metricScalarAt (K.toHistory.stageMetric j v) y) (Iic s) s| ≤
        Ctime * metricScalarAt (K.toHistory.stageMetric j s) y ^ 2) ∧
    ∀ v : TangentSpace I3 y,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (K.toHistory.stageMetric j s)) y v)| ≤
      Cgrad * metricScalarAt (K.toHistory.stageMetric j s) y *
        Real.sqrt (metricScalarAt (K.toHistory.stageMetric j s) y) *
        Real.sqrt ((K.toHistory.stageMetric j s).inner y v v) := by
  have onSlab : ∀ {Q : OrientedThreeStage.{u}} {a b : ℝ} (G : Q.IncomingSlab a b),
      G.DerivativeBoundBefore Ctime qcan b → G.GradientBoundBefore Cgrad qcan b →
      ∀ (t : ℝ), t ∈ Ico a b → ∀ (x : Q.Carrier), qcan < G.flow.scalar t x →
      (a < t → |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤
        Ctime * G.flow.scalar t x ^ 2) ∧
      ∀ v : TangentSpace I3 x,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t x v| ≤
          Cgrad * G.flow.scalar t x * Real.sqrt (G.flow.scalar t x) *
            Real.sqrt ((G.flow.base.metric t).inner x v v) := by
    intro Q a b G hder hgrad t ht x hx
    refine ⟨fun hstrict => hder x t ⟨hstrict, ht.2⟩ hx, ?_⟩
    rcases eq_or_lt_of_le ht.1 with heq | hstrict
    · subst t
      exact G.abs_scalarDifferential_le_at_birth_of_gradientBoundBefore hqcan hgrad x hx
    · exact hgrad x t ⟨hstrict, ht.2⟩ hx
  cases j using Fin.lastCases with
  | last =>
    rw [K.toHistory.stageEndTime_last] at hs
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon := hs.1.trans_lt hs.2
    let G := (K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl
    have hfun : K.toHistory.stageMetric (Fin.last K.eventCount) =
        (K.finalSlab hfinal).flow.base.metric := funext fun τ =>
      ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfinal) τ
    rw [hfun] at hscalar ⊢
    exact onSlab G (hEst.2 hfinal).1 (hEst.2 hfinal).2.1 s hs y hscalar
  | cast i =>
    rw [K.toHistory.stageEndTime_castSucc] at hs
    have hfun : K.toHistory.stageMetric i.castSucc =
        (K.toHistory.event i).incoming.flow.base.metric := funext fun τ =>
      ObservedHistory.stageMetric_castSucc_apply (H := K.toHistory) i τ
    rw [hfun] at hscalar ⊢
    exact onSlab (K.toHistory.event i).incoming (hEst.1 i).1 (hEst.1 i).2.1 s hs y hscalar

end GC.GeneralFlow
