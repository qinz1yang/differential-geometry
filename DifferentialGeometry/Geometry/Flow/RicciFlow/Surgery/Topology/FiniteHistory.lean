import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent

noncomputable section

open Bundle Manifold
open DifferentialGeometry.Topology (ClosedOrientedManifold FiniteCutCapTrace)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

structure FiniteSurgeryHistory where
  eventCount : ℕ
  eventCount_pos : 0 < eventCount
  time : Fin (eventCount + 1) → ℝ
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  stage : Fin (eventCount + 1) → ClosedOrientedManifold.{u} 3
  initialMetric : (i : Fin (eventCount + 1)) → SmoothRiemannianMetric (𝓡 3) (stage i).Carrier
  event : (i : Fin eventCount) →
    MetricCutCapEvent (stage i.castSucc) (stage i.succ) (time i.castSucc) (time i.succ)
  event_initial : ∀ i : Fin eventCount,
    (event i).incoming.flow.base.metric (time i.castSucc) = initialMetric i.castSucc
  event_output : ∀ i : Fin eventCount, (event i).outputMetric = initialMetric i.succ

namespace FiniteSurgeryHistory

variable (H : FiniteSurgeryHistory.{u})

def cutCapTrace : FiniteCutCapTrace.{u} where
  eventCount := H.eventCount
  eventCount_pos := H.eventCount_pos
  stage := H.stage
  transition i := (H.event i).transition

def terminalTime : ℝ := H.time (Fin.last H.eventCount)

def extinctAt (T : ℝ) : Prop :=
  T = H.terminalTime ∧ IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

def controlledBy
    (D : (M : ClosedOrientedManifold.{u} 3) → ConnectedComponents M.Carrier → Prop) : Prop :=
  H.cutCapTrace.controlledBy D

structure InitialIdentification (M : ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) where
  diffeomorph : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (H.stage 0).Carrier
  orientation_preserving : diffeomorph.preservesOrientation M.orientation (H.stage 0).orientation
  metric_eq : ∀ x : M.Carrier, ∀ v w : TangentSpace (𝓡 3) x,
    (H.initialMetric 0).inner (diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x v)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x w) = g.inner x v w

def InitialIdentification.cutCapIdentification
    {M : ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (f : H.InitialIdentification M g) : H.cutCapTrace.InitialIdentification M :=
  ⟨f.diffeomorph, f.orientation_preserving⟩

theorem stage_nonempty (i : Fin H.eventCount) : Nonempty (H.stage i.castSucc).Carrier :=
  (H.event i).transition.source_nonempty

theorem terminalTime_pos : 0 < H.terminalTime := by
  rw [← H.time_zero]
  apply H.time_strictMono
  exact H.eventCount_pos

theorem extinct_trace {T : ℝ} (h : H.extinctAt T) : H.cutCapTrace.extinct := h.2

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery
