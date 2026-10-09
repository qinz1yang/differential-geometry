import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.HistoryParabolicBallPrefixTransport

set_option autoImplicit false

/-!
# CX-SPINE G23：完整 small seed 的 SamePresentation 运输

复用已核查 HistoryParabolicBallPrefixTransport:54–126 的结构识别与真实 crossing/terminal 叶子。
空间半径仍r、时间深度仍r²；仅trace的控制半径是√3*r，不能替换成controlledBall(√3*r)。
ordinary分支在activeStage_mem上用metric等式，terminal分支使用真实incoming terminal曲率等式。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

open private regularCrossing_iff_of_samePresentation
  terminal_curvature_normSq_eq_of_samePresentation from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingPresentation.Basic

namespace GC.LongTime.Ch11

universe u

/-- 同一 presentation 保持完整 small seed，包括全部 surgery terminal 曲率界。 -/
theorem smallParabolicCurvature_of_samePresentation_CXSP
    {H K : ObservedHistory.{u}} (R : H.SamePresentation K)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier)
    (q : (K.stageAt ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩).Carrier)
    (hpq : HEq q p) (r : ℝ)
    (hseed : hasSmallParabolicCurvature K
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ q r) :
    hasSmallParabolicCurvature H t p r := by
  rcases H with ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
    eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  rcases K with ⟨T', hT', n', times', htimes', hzero', hlast', stages', initialK,
    eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  have hhorizon : T = T' := R.horizon_eq
  subst T'
  have hcount : n = n' := R.count_eq
  subst n'
  have htime : times = times' := funext fun j => R.time_eq j
  subst times'
  have hstage : stages = stages' := funext fun j => R.stage_eq j
  subst stages'
  have hqp : q = p := eq_of_heq hpq
  subst q
  let L : ObservedHistory.{u} :=
    ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
      eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  let K : ObservedHistory.{u} :=
    ⟨T, hT', n, times, htimes', hzero', hlast', stages, initialK,
      eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  change L.SamePresentation K at R
  change hasSmallParabolicCurvature K t p r at hseed
  change hasSmallParabolicCurvature L t p r
  have hmetric (j : Fin (n + 1)) (v : ℝ) (hv : v ∈ L.stageDomain j) :
      L.stageMetric j v = K.stageMetric j v :=
    eq_of_heq (R.metric_heq j v hv)
  obtain ⟨hrpos, a, hat, ha, htraces⟩ := hseed
  refine ⟨hrpos, a, hat, ha, ?_⟩
  intro x hx
  have hxK : x ∈ riemannianBallOf (K.stageMetric (K.activeStage t) t) p r := by
    change x ∈ riemannianBallOf (K.stageMetric (L.activeStage t) t) p r
    rw [← hmetric (L.activeStage t) t (L.activeStage_mem t)]
    exact hx
  obtain ⟨A, hA⟩ := htraces x hxK
  let B : BackwardPointTrace L (L.activeStage a) (L.activeStage t)
      (L.activeStage_mono hat) x :=
    { point := fun j hf hl => A.point j hf hl
      endpoint_eq := A.endpoint_eq
      crossing := fun i hf hl =>
        (regularCrossing_iff_of_samePresentation (R.event_eq i) _ _).mpr (A.crossing i hf hl) }
  refine ⟨B, ?_, ?_⟩
  · intro v hav hvt
    change (Real.sqrt 3 * r) ^ 4 * normSq0S (L.stageMetric (L.activeStage v) v)
      (A.point (L.activeStage v) (L.activeStage_mono hav) (L.activeStage_mono hvt)) 4
      (metricRm04At (L.stageMetric (L.activeStage v) v)
        (A.point (L.activeStage v) (L.activeStage_mono hav) (L.activeStage_mono hvt))) ≤ 1
    rw [hmetric (L.activeStage v) v (L.activeStage_mem v)]
    exact hA.1 v hav hvt
  · intro i hf hl
    let yL : (L.event i).incoming.terminalRegularOpen :=
      ⟨B.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (B.crossing i hf hl).mem_terminalRegularRegion (L.event i)⟩
    let yK : (K.event i).incoming.terminalRegularOpen :=
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion (K.event i)⟩
    have hnorm : normSq0S (L.event i).terminal.metric yL 4
        (metricRm04At (L.event i).terminal.metric yL) =
        normSq0S (K.event i).terminal.metric yK 4
          (metricRm04At (K.event i).terminal.metric yK) :=
      terminal_curvature_normSq_eq_of_samePresentation (R.event_eq i)
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) yL.property yK.property
    change (Real.sqrt 3 * r) ^ 4 * normSq0S (L.event i).terminal.metric yL 4
      (metricRm04At (L.event i).terminal.metric yL) ≤ 1
    rw [hnorm]
    exact hA.2 i hf hl

end GC.LongTime.Ch11
