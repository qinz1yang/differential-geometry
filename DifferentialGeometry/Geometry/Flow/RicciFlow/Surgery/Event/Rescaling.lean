import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabRescaling

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a b : ℝ}

private theorem cast_continuousMap_val {X : Type*} [TopologicalSpace X]
    {U V : TopologicalSpace.Opens P.Carrier} (h : U = V) (f : C(X, U)) (x : X) :
    ((h ▸ f) x).1 = (f x).1 := by
  cases h
  rfl

private theorem cast_metric_inner {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 3) X]
    {U V : TopologicalSpace.Opens P.Carrier} (h : U = V)
    (q : ∀ U : TopologicalSpace.Opens P.Carrier, SmoothRiemannianMetric ThreeModel U → Prop)
    (g : {g : SmoothRiemannianMetric ThreeModel U // q U g}) (f : C(X, U))
    (x : X) (v w : TangentSpace (𝓡∂ 3) x) :
    (h ▸ g).1.inner ((h ▸ f) x)
        (mfderiv (𝓡∂ 3) ThreeModel (h ▸ f) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (h ▸ f) x w) =
      g.1.inner (f x) (mfderiv (𝓡∂ 3) ThreeModel f x v)
        (mfderiv (𝓡∂ 3) ThreeModel f x w) := by
  cases h
  rfl

def rescale (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    MetricCutCapEvent P Q (a / r) (b / r) where
  discarded := E.discarded
  capped := E.capped
  transition := E.transition
  incoming := E.incoming.rescale r hr
  terminal := E.terminal.rescale r hr
  outputMetric := scaleMetric r⁻¹ (inv_pos.mpr hr) E.outputMetric
  old := E.old
  old_compact := E.old_compact
  old_retained := E.old_retained
  oldCharts := E.oldCharts
  oldSmooth := E.oldSmooth
  old_induced := E.old_induced
  oldTerminal := (E.incoming.rescale_terminalRegularOpen r hr).symm ▸ E.oldTerminal
  oldTerminal_eq := by
    intro x
    exact (cast_continuousMap_val _ E.oldTerminal x).trans (E.oldTerminal_eq x)
  oldOutput := E.oldOutput
  oldOutput_eq := E.oldOutput_eq
  old_metric_eq := by
    let _ := E.oldCharts
    intro x v w
    let q (U : TopologicalSpace.Opens P.Carrier) (gbar : SmoothRiemannianMetric ThreeModel U) :=
      ∀ K : Set U, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ d ∈ Ico (a / r) (b / r), ∀ t ∈ Ioo d (b / r), ∀ y ∈ K,
          DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
            (((E.incoming.rescale r hr).flow.base.metric t).restrictOpen U) gbar gbar y < ε
    let old : {gbar : SmoothRiemannianMetric ThreeModel E.incoming.terminalRegularOpen //
        q E.incoming.terminalRegularOpen gbar} :=
      ⟨scaleMetric r⁻¹ (inv_pos.mpr hr) E.terminal.metric, E.terminal.rescale_converges r hr⟩
    have ht := cast_metric_inner (E.incoming.rescale_terminalRegularOpen r hr).symm
      q old E.oldTerminal x v w
    apply ht.trans
    simpa only [old, scaleMetric_inner] using
      congrArg (fun z : ℝ => r⁻¹ * z) (E.old_metric_eq x v w)
  old_contains_outside := E.old_contains_outside
  every_child_meets_old := E.every_child_meets_old

@[simp] theorem rescale_discarded (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).discarded = E.discarded := rfl

@[simp] theorem rescale_capped (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).capped = E.capped := rfl

@[simp] theorem rescale_transition (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).transition = E.transition := rfl

@[simp] theorem rescale_incoming_metric (E : MetricCutCapEvent P Q a b)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (E.rescale r hr).incoming.flow.base.metric t =
      scaleMetric r⁻¹ (inv_pos.mpr hr) (E.incoming.flow.base.metric (r * t)) :=
  E.incoming.rescale_metric r hr t

@[simp] theorem rescale_outputMetric (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).outputMetric = scaleMetric r⁻¹ (inv_pos.mpr hr) E.outputMetric := rfl

@[simp] theorem rescale_old (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).old = E.old := rfl

@[simp] theorem rescale_oldOutput (E : MetricCutCapEvent P Q a b) (r : ℝ) (hr : 0 < r) :
    (E.rescale r hr).oldOutput = E.oldOutput := rfl

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
