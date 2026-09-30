import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

private def retainedToOld (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    C((E.transition.retainedCoreOpens : Type u), E.old) where
  toFun x := ⟨x.1, hOld ▸ x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem contMDiff_retainedToOld (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    letI := E.oldCharts
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (E.retainedToOld hOld) := by
  let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  let := E.oldCharts
  let := E.transition.coreCharts
  let := E.transition.coreSmooth
  have hinc := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
    (𝓡∂ 3) ThreeModel _ E.transition.core_induced E.transition.retainedCoreOpens
  change ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (E.retainedToOld hOld)
  intro x
  rw [ContMDiffAt.iff_comp_isImmersionAt
    (E.old_induced.isImmersion.isImmersionAt (E.retainedToOld hOld x))]
  exact ⟨(E.retainedToOld hOld).continuous.continuousAt, hinc.contMDiff.contMDiffAt⟩

def retainedOldDiffeomorph (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    letI := E.oldCharts
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.transition.retainedCoreOpens E.old ∞ := by
  letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  letI := E.oldCharts
  let back : C(E.old, (E.transition.retainedCoreOpens : Type u)) :=
    ⟨fun x => ⟨x.1, by change x.1 ∈ E.transition.trace.retainedCore; rw [← hOld]; exact x.2⟩,
      continuous_subtype_val.subtype_mk (fun x => by
        change x.1 ∈ E.transition.trace.retainedCore
        rw [← hOld]
        exact x.2)⟩
  refine ⟨⟨E.retainedToOld hOld, back, fun _ => rfl, fun _ => rfl⟩,
    E.contMDiff_retainedToOld hOld, ?_⟩
  let := E.transition.coreCharts
  let := E.transition.coreSmooth
  have hinc := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
    (𝓡∂ 3) ThreeModel _ E.transition.core_induced E.transition.retainedCoreOpens
  change ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ back
  intro x
  rw [ContMDiffAt.iff_comp_isImmersionAt (hinc.isImmersion.isImmersionAt (back x))]
  exact ⟨back.continuous.continuousAt, E.old_induced.contMDiff.contMDiffAt⟩

def toRetainedCoreEvent (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) : RetainedCoreEvent P Q a s where
  discarded := E.discarded
  capped := E.capped
  transition := E.transition
  incoming := E.incoming
  terminal := E.terminal
  outputMetric := E.outputMetric
  oldTerminal := E.oldTerminal.comp (E.retainedToOld hOld)
  oldTerminal_eq := fun x => E.oldTerminal_eq (E.retainedToOld hOld x)
  oldOutput := E.oldOutput.comp (E.retainedToOld hOld)
  oldOutput_eq := fun x => E.oldOutput_eq (E.retainedToOld hOld x)
  old_metric_eq := by
    let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    let := E.oldCharts
    intro x v w
    have hterminal := E.oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiable (by simp)
    have houtput := E.contMDiff_oldOutput.mdifferentiable (by simp)
    have hmap := (E.contMDiff_retainedToOld hOld).mdifferentiable (by simp)
    change E.terminal.metric.inner _
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldTerminal ∘ E.retainedToOld hOld) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldTerminal ∘ E.retainedToOld hOld) x w) =
      E.outputMetric.inner _
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldOutput ∘ E.retainedToOld hOld) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldOutput ∘ E.retainedToOld hOld) x w)
    rw [mfderiv_comp x (hterminal _) (hmap _), mfderiv_comp x (houtput _) (hmap _)]
    exact E.old_metric_eq (E.retainedToOld hOld x) _ _
  every_child_meets_old := by
    intro c
    obtain ⟨x, hx⟩ := E.every_child_meets_old c
    exact ⟨⟨x.1, by change x.1 ∈ E.transition.trace.retainedCore; rw [← hOld]; exact x.2⟩, hx⟩

@[simp] theorem toRetainedCoreEvent_transition (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).transition = E.transition := rfl

@[simp] theorem toRetainedCoreEvent_incoming (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).incoming = E.incoming := rfl

@[simp] theorem toRetainedCoreEvent_terminal (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).terminal = E.terminal := rfl

@[simp] theorem toRetainedCoreEvent_outputMetric (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).outputMetric = E.outputMetric := rfl

theorem regularCrossing_toRetainedCoreEvent_iff (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) (p : P.Carrier) (q : Q.Carrier) :
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.RegularCrossing p q ↔
      E.RegularCrossing p q := by
  let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  let := E.oldCharts
  let d := E.retainedOldDiffeomorph hOld
  constructor
  · rintro ⟨x, hx, hp, hq⟩
    refine ⟨d x, ((d.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hx, ?_, ?_⟩
    · change x.1.1 = p
      exact hp
    · convert hq using 1
      rfl
  · rintro ⟨x, hx, hp, hq⟩
    refine ⟨d.symm x, ((d.symm.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hx,
      ?_, ?_⟩
    · change x.1.1 = p
      exact hp
    · change E.oldOutput _ = q
      convert hq using 1
      rfl

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
