import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem regularCrossing_iff_of_samePresentation
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F)
    (p : P.Carrier) (q : Q.Carrier) : E.RegularCrossing p q ↔ F.RegularCrossing p q := by
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq R.old_heq
  cases eq_of_heq R.oldCharts_heq
  cases eq_of_heq R.oldOutput_heq
  rfl

private theorem curvature_normSq_eq_of_open_eq
    {P : OrientedThreeStage.{u}} {U V : TopologicalSpace.Opens P.Carrier}
    (hUV : U = V) (gU : SmoothRiemannianMetric ThreeModel U)
    (gV : SmoothRiemannianMetric ThreeModel V) (hg : HEq gU gV)
    (p : P.Carrier) (hpU : p ∈ U) (hpV : p ∈ V) :
    normSq0S gU ⟨p, hpU⟩ 4 (metricRm04At gU ⟨p, hpU⟩) =
      normSq0S gV ⟨p, hpV⟩ 4 (metricRm04At gV ⟨p, hpV⟩) := by
  cases hUV
  cases eq_of_heq hg
  rfl

private theorem terminal_curvature_normSq_eq_of_samePresentation
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    {E F : MetricCutCapEvent P Q a s} (R : E.SamePresentation F)
    (p : P.Carrier) (hpE : p ∈ E.incoming.terminalRegularOpen)
    (hpF : p ∈ F.incoming.terminalRegularOpen) :
    normSq0S E.terminal.metric ⟨p, hpE⟩ 4
        (metricRm04At E.terminal.metric ⟨p, hpE⟩) =
      normSq0S F.terminal.metric ⟨p, hpF⟩ 4
        (metricRm04At F.terminal.metric ⟨p, hpF⟩) :=
  curvature_normSq_eq_of_open_eq (eq_of_heq R.terminalRegion_heq)
    E.terminal.metric F.terminal.metric R.terminalMetric_heq p hpE hpF

private theorem noncollapsedBefore_of_samePresentation
    {H K : RetainedCoreHistory.{u}} (R : H.toHistory.SamePresentation K.toHistory)
    {κ ρ t₀ : ℝ} (hnc : H.NoncollapsedBefore κ ρ t₀) :
    K.NoncollapsedBefore κ ρ t₀ := by
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
  let LH : RetainedCoreHistory.{u} :=
    ⟨T, hT, n, times, htimes, hzero, hlast, stages, initialH,
      eventsH, hinitialH, houtputH, finalH, hfinalH⟩
  let KH : RetainedCoreHistory.{u} :=
    ⟨T, hT', n, times, htimes', hzero', hlast', stages, initialK,
      eventsK, hinitialK, houtputK, finalK, hfinalK⟩
  let L := LH.toHistory
  let K := KH.toHistory
  change L.SamePresentation K at R
  change LH.NoncollapsedBefore κ ρ t₀ at hnc
  change KH.NoncollapsedBefore κ ρ t₀
  have hmetric (j : Fin (n + 1)) (v : ℝ) (hv : v ∈ L.stageDomain j) :
      L.stageMetric j v = K.stageMetric j v :=
    eq_of_heq (R.metric_heq j v hv)
  intro t p r ht hr hball
  have hballL : L.isParabolicallyRmControlledBall t p r := by
    obtain ⟨hrpos, a, hat, ha, htraces⟩ := hball
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
    · intro s has hst
      change r ^ 4 * normSq0S (L.stageMetric (L.activeStage s) s)
        (A.point (L.activeStage s) (L.activeStage_mono has) (L.activeStage_mono hst)) 4
        (metricRm04At (L.stageMetric (L.activeStage s) s)
          (A.point (L.activeStage s) (L.activeStage_mono has) (L.activeStage_mono hst))) ≤ 1
      rw [hmetric (L.activeStage s) s (L.activeStage_mem s)]
      exact hA.1 s has hst
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
      change r ^ 4 * normSq0S (L.event i).terminal.metric yL 4
        (metricRm04At (L.event i).terminal.metric yL) ≤ 1
      rw [hnorm]
      exact hA.2 i hf hl
  have hvolume := hnc t p r ht hr hballL
  rw [hmetric (L.activeStage t) t (L.activeStage_mem t)] at hvolume
  exact hvolume

namespace RetainedCoreHistory

theorem noncollapsedBefore_iff_of_samePresentation
    {H K : RetainedCoreHistory.{u}} (R : H.toHistory.SamePresentation K.toHistory)
    (κ ρ t₀ : ℝ) : H.NoncollapsedBefore κ ρ t₀ ↔ K.NoncollapsedBefore κ ρ t₀ :=
  ⟨noncollapsedBefore_of_samePresentation R, noncollapsedBefore_of_samePresentation R.symm⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
