import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

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

noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u



abbrev FiniteSurgeryHistory :=
  {H : ObservedHistory.{u} // 0 < H.eventCount ∧ H.horizon = H.time (Fin.last H.eventCount)}

namespace ObservedHistory

variable (H : ObservedHistory.{u})


theorem restrict_last_eventCount :
    (H.restrict (H.stageTime (Fin.last H.eventCount))).eventCount = H.eventCount := by
  rw [restrict_eventCount, stageTime, activeStage_at_time]
  rfl


theorem eventCount_pos_of_final_empty [Nonempty (H.stage 0).Carrier]
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] : 0 < H.eventCount := by
  apply Nat.pos_of_ne_zero
  intro hn
  have he : Fin.last H.eventCount = (0 : Fin (H.eventCount + 1)) := Fin.ext hn
  have hne : Nonempty (H.stage (Fin.last H.eventCount)).Carrier := he ▸ inferInstance
  exact not_nonempty_iff.mpr inferInstance hne


theorem last_time_pos (hn : 0 < H.eventCount) : 0 < H.time (Fin.last H.eventCount) := by
  rw [← H.time_zero]
  exact H.time_strictMono (by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hn)



def toFiniteHistory (hn : 0 < H.eventCount) : FiniteSurgeryHistory.{u} := by
  let F := H.restrict (H.stageTime (Fin.last H.eventCount))
  have hc : F.eventCount = H.eventCount := H.restrict_last_eventCount
  refine ⟨F, hc ▸ hn, ?_⟩
  change H.time (Fin.last H.eventCount) =
    H.time (Fin.castLE _ (Fin.last F.eventCount))
  congr 1
  exact Fin.ext hc.symm


@[simp] theorem toFiniteHistory_eventCount (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.eventCount = H.eventCount := H.restrict_last_eventCount


@[simp] theorem toFiniteHistory_horizon (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.horizon = H.time (Fin.last H.eventCount) := rfl


theorem toFiniteHistory_finalStage (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.stage (Fin.last (H.toFiniteHistory hn).1.eventCount) =
      H.stage (Fin.last H.eventCount) := by
  change H.stage (Fin.castLE _ (Fin.last (H.toFiniteHistory hn).1.eventCount)) = _
  apply congrArg H.stage
  exact Fin.ext (H.toFiniteHistory_eventCount hn)


theorem toFiniteHistory_isPrefixOf (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.IsPrefixOf H := H.restrict_isPrefixOf _




theorem toFiniteHistory_discards
    (hn : 0 < H.eventCount) (D : OrientedThreeStage.{u} → Prop)
    (hD : ∀ i : Fin H.eventCount, D (H.event i).discarded) :
    ∀ i : Fin (H.toFiniteHistory hn).1.eventCount,
      D ((H.toFiniteHistory hn).1.event i).discarded := by
  intro i
  exact hD (Fin.castLE _ i)



theorem exists_extinct_finiteHistory [Nonempty (H.stage 0).Carrier]
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] :
    ∃ F : FiniteSurgeryHistory.{u},
      F.1 = H.restrict (H.stageTime (Fin.last H.eventCount)) ∧
      F.1.eventCount = H.eventCount ∧
      F.1.horizon = H.time (Fin.last H.eventCount) ∧
      0 < F.1.horizon ∧ F.1.horizon ≤ H.horizon ∧
      IsEmpty (F.1.stage (Fin.last F.1.eventCount)).Carrier := by
  let hn := H.eventCount_pos_of_final_empty
  refine ⟨H.toFiniteHistory hn, rfl, H.toFiniteHistory_eventCount hn, rfl,
    H.last_time_pos hn, H.time_le_horizon, ?_⟩
  rw [H.toFiniteHistory_finalStage hn]
  infer_instance

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}



theorem initial_nonempty (A : InitialIdentification P g H) [Nonempty P.Carrier] :
    Nonempty (H.stage 0).Carrier := Nonempty.map A.map inferInstance


def toFiniteHistory (A : InitialIdentification P g H) (hn : 0 < H.eventCount) :
    InitialIdentification P g (H.toFiniteHistory hn).1 := A.restrict _


@[simp] theorem toFiniteHistory_map (A : InitialIdentification P g H)
    (hn : 0 < H.eventCount) : (A.toFiniteHistory hn).map = A.map := rfl


theorem toFiniteHistory_isPrefixOf (A : InitialIdentification P g H)
    (hn : 0 < H.eventCount) : (A.toFiniteHistory hn).IsPrefixOf A :=
  A.restrict_isPrefixOf _

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
