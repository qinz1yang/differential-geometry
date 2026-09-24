import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Assembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Topology.Manifold.CollarFamily
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.VanKampen.FullGroupoid

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem disjointBoundaryCollarFamily_holds :
    disjointBoundaryCollarFamily.{u} := by
  intro X _ _ ι _ S _ _ e c hc h0 hdisj
  exact DifferentialGeometry.Topology.Collar.disjointBoundaryCollarFamily hc h0 hdisj

theorem seifertVanKampenPushout_holds :
    seifertVanKampenPushout.{u} := by
  intro X _ U V hU hV hcover
  exact DifferentialGeometry.Topology.VanKampen.seifertVanKampen U V hU hV hcover

theorem boundaryCollarGeometry_iff :
    boundaryCollarGeometry.{u} ↔ relativeCollarUniqueness.{u} :=
  ⟨fun h => h.2, fun h => ⟨disjointBoundaryCollarFamily_holds, h⟩⟩

theorem geometricReconstructionBackground_iff :
    geometricReconstructionBackground.{u} ↔
      relativeCollarUniqueness.{u} ∧ ballEmbeddingIsotopy.{u} ∧
        sphereDiffeomorphismIsotopyConnected :=
  ⟨fun h => ⟨h.1.2, h.2.1, h.2.2.1⟩,
    fun h => ⟨⟨disjointBoundaryCollarFamily_holds, h.1⟩, h.2.1, h.2.2,
      seifertVanKampenPushout_holds⟩⟩

theorem globalMetricStep_iff_globalStepConclusion
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :
    globalMetricStep p τ ε d k a₀ DiscardedCutOpen inputs ↔
      GlobalStepConclusion.{u} p τ ε d k a₀ DiscardedCutOpen inputs :=
  Iff.rfl

theorem globalMetricStep_scale_positive
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (a₀ : ℝ)
    (DiscardedCutOpen : Type u → Prop)
    (inputs : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
    (h : globalMetricStep p τ ε d k a₀ DiscardedCutOpen inputs) :
    ∃ hstar : ℝ, 0 < hstar ∧ 2 * hstar ^ 2 < τ := by
  obtain ⟨hstar, hpos, hlt, _⟩ := h
  exact ⟨hstar, hpos, hlt⟩

def TangentOrientationSection.toManifoldOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) : ManifoldOrientation ThreeModel M 3 where
  dimension_eq := by simp
  orientation := o.orientation
  locally_constant := o.locally_constant

theorem mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective
    {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) :
    (f.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (f.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (f x)) v =
    mfderiv ThreeModel ThreeModel f x v
  rfl

theorem preservesOrientation_of_preservesTangentOrientation
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (oM : TangentOrientationSection M)
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (oN : TangentOrientationSection N)
    (f : M ≃ₘ⟮ThreeModel, ThreeModel⟯ N)
    (h : PreservesTangentOrientation oM oN f) :
    f.preservesOrientation oM.toManifoldOrientation oN.toManifoldOrientation := by
  intro x
  obtain ⟨hf, hfx⟩ := h.2 x
  rw [mfderivToContinuousLinearEquiv_toLinearEquiv_eq_ofBijective f x hf]
  exact hfx

theorem OrientedThreeStage.preservesOrientation_toClosedOrientedManifold
    {P Q : OrientedThreeStage.{u}} {f : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier}
    (h : PreservesTangentOrientation P.orientation Q.orientation f) :
    f.preservesOrientation P.toClosedOrientedManifold.orientation
      Q.toClosedOrientedManifold.orientation := by
  intro x
  exact preservesOrientation_of_preservesTangentOrientation
    P.orientation Q.orientation f h x

def InitialIdentification.toFiniteSurgeryHistory
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) (hn : 0 < H.eventCount)
    (bridge : (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc).toClosedOrientedManifold
        (H.stage i.succ).toClosedOrientedManifold
        (H.time i.castSucc) (H.time i.succ))
    (hbridge_initial : ∀ i : Fin H.eventCount,
      (bridge i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc)
    (hbridge_output : ∀ i : Fin H.eventCount,
      (bridge i).outputMetric = H.initialMetric i.succ) :
    (H.toSurgeryFiniteSurgeryHistory hn bridge hbridge_initial hbridge_output).InitialIdentification
      P.toClosedOrientedManifold g where
  diffeomorph := A.map
  orientation_preserving :=
    OrientedThreeStage.preservesOrientation_toClosedOrientedManifold A.positive
  metric_eq := A.metric_eq

theorem exists_poincare_controlled_extinction_of_observedHistory
    (P : OrientedThreeStage.{u}) (g : P.Metric) (H : ObservedHistory.{u})
    (A : InitialIdentification P g H) [Nonempty P.Carrier]
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ i : Fin H.eventCount, ∀ c : ConnectedComponents (H.event i).discarded.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        ((H.event i).discarded.toClosedOrientedManifold.component c).Carrier)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  have hn : 0 < H.eventCount :=
    @ObservedHistory.eventCount_pos_of_final_empty H A.initial_nonempty hempty
  refine ⟨{ history := H.toSurgeryFiniteSurgeryHistory_of_cutCapCompletion hn hc hout
            time := H.time (Fin.last H.eventCount)
            time_pos := H.last_time_pos hn
            initial := A.toFiniteSurgeryHistory hn (H.toSurgeryEvents hc hout)
              (H.toSurgeryEvents_initial hc hout) (H.toSurgeryEvents_output hc hout)
            controlled := ?_
            extinct := ?_ }⟩
  · intro i
    exact SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled
      (H.event i).transition (hc i) (hctrl i)
  · exact ⟨rfl, hempty⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
