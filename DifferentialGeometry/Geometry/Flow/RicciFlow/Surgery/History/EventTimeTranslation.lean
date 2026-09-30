import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TerminalTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ActualEventGeometry
set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff
namespace GC.GeneralFlow
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem transfer_old_metric {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N)
    (U V : TopologicalSpace.Opens P.Carrier) (hUV : U = V)
    (m : SmoothRiemannianMetric ThreeModel U) (g : Q.Metric)
    (f : C((X.retainedCoreOpens : Type u), U))
    (o : C((X.retainedCoreOpens : Type u), Q.Carrier))
    (hf : ∀ x, (f x).1 = x.1.1)
    (heq : letI := X.coreOpensCharts X.retainedCoreOpens
      ∀ (x : X.retainedCoreOpens) (v w : TangentSpace (𝓡∂ 3) x),
        m.inner (f x) (mfderiv (𝓡∂ 3) ThreeModel f x v)
          (mfderiv (𝓡∂ 3) ThreeModel f x w) =
        g.inner (o x) (mfderiv (𝓡∂ 3) ThreeModel o x v)
          (mfderiv (𝓡∂ 3) ThreeModel o x w)) :
    ∃ f' : C((X.retainedCoreOpens : Type u), V), (∀ x, (f' x).1 = x.1.1) ∧
      (letI := X.coreOpensCharts X.retainedCoreOpens
      ∀ (x : X.retainedCoreOpens) (v w : TangentSpace (𝓡∂ 3) x),
        (hUV ▸ m).inner (f' x) (mfderiv (𝓡∂ 3) ThreeModel f' x v)
          (mfderiv (𝓡∂ 3) ThreeModel f' x w) =
        g.inner (o x) (mfderiv (𝓡∂ 3) ThreeModel o x v)
          (mfderiv (𝓡∂ 3) ThreeModel o x w)) := by
  cases hUV
  exact ⟨f,hf,heq⟩

def translate_retained_event {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    RetainedCoreEvent P Q (a+c) (s+c) := by
  let data := transfer_old_metric E.transition E.incoming.terminalRegularOpen
    (E.incoming.timeTranslate c).terminalRegularOpen
    (translated_terminal_open E.incoming c).symm E.terminal.metric E.outputMetric
    E.oldTerminal E.oldOutput E.oldTerminal_eq E.old_metric_eq
  exact {
    discarded := E.discarded
    capped := E.capped
    transition := E.transition
    incoming := E.incoming.timeTranslate c
    terminal := translate_terminal_metric E.terminal c
    outputMetric := E.outputMetric
    oldTerminal := Classical.choose data
    oldTerminal_eq := (Classical.choose_spec data).1
    oldOutput := E.oldOutput
    oldOutput_eq := E.oldOutput_eq
    old_metric_eq := (Classical.choose_spec data).2
    every_child_meets_old := E.every_child_meets_old }

@[simp] theorem translated_event_transition {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    (translate_retained_event E c).transition = E.transition := rfl

@[simp] theorem translated_event_output {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    (translate_retained_event E c).outputMetric = E.outputMetric := rfl

theorem translated_event_initial {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    (translate_retained_event E c).incoming.flow.base.metric (a+c) =
      E.incoming.flow.base.metric a :=
  E.incoming.timeTranslate_initial_metric c

theorem translated_event_singular {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ) :
    (translate_retained_event E c).incoming.SingularEndpoint ↔ E.incoming.SingularEndpoint :=
  E.incoming.timeTranslate_singularEndpoint_iff c

theorem translated_event_actual_geometry {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : RetainedCoreEvent P Q a s) (c : ℝ)
    (hb : E.transition.boundaryFrameReversing)
    (hd : E.toMetricCutCapEvent.poincareStandardDiscarded) :
    GC.Surgery.ActualMetricEventGeometry (translate_retained_event E c).toMetricCutCapEvent :=
  GC.Surgery.actual_metric_event_geometry (translate_retained_event E c).toMetricCutCapEvent hb hd

end GC.GeneralFlow
