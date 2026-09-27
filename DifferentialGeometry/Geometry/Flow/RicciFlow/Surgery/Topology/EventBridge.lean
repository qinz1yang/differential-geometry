import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def OrientedThreeStage.IncomingSlab.toSurgery {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.IncomingSlab
      P.toClosedOrientedManifold a s where
  lt := G.lt
  flow := G.flow
  equation := G.equation
  smoothUpTo := G.smoothUpTo

def OrientedThreeStage.IncomingSlab.TerminalLimitMetric.toSurgery
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) :
    (G.toSurgery).TerminalLimitMetric where
  metric := L.metric
  converges := L.converges

theorem OrientedThreeStage.IncomingSlab.toSurgery_lt {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).lt = G.lt := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_flow {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : (G.toSurgery).flow = G.flow := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_equation {P : OrientedThreeStage.{u}}
    {a s : ℝ} (G : P.IncomingSlab a s) : (G.toSurgery).equation = G.equation := rfl

theorem OrientedThreeStage.IncomingSlab.TerminalLimitMetric.toSurgery_metric
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) : (L.toSurgery).metric = L.metric := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_terminalRegularRegion
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularRegion = G.terminalRegularRegion := rfl

theorem OrientedThreeStage.IncomingSlab.toSurgery_terminalRegularOpen
    {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) :
    (G.toSurgery).terminalRegularOpen = G.terminalRegularOpen := rfl

def SphericalTubeSystem.ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    DifferentialGeometry.Topology.SphericalTubeSystem P.toClosedOrientedManifold where
  Index := X.trace.tubes.Index
  finiteIndex := X.trace.tubes.finiteIndex
  tube := X.trace.tubes.tube
  smooth := X.tube_smooth
  disjoint := X.trace.tubes.disjoint

theorem SphericalTubeSystem.core_ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).core = X.trace.tubes.core := rfl

theorem SphericalTubeSystem.removedBand_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (a : X.trace.tubes.Index) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).removedBand a =
      X.trace.tubes.removedBand a := rfl

theorem SphericalTubeSystem.mem_surgeryRegion_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (x : X.trace.tubes.core) :
    x.1 ∈ (SphericalTubeSystem.ofSmoothCutCapTransition X).surgeryRegion ↔
      ∃ a : X.trace.tubes.Index,
        x.1 ∈ X.trace.tubes.tube a ''
          {z : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain |
            (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2} := by
  rw [DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion]
  exact Set.mem_iUnion

theorem SmoothCutCapTransition.presentation_linearEquiv_eq {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (x : N.Carrier)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x)) :
    (X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (X.presentation.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (X.presentation x)) v =
    mfderiv ThreeModel ThreeModel X.presentation x v
  rfl

theorem SmoothCutCapTransition.presentation_positive_toSurgery {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.toClosedOrientedManifold.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.toClosedOrientedManifold.orientation.orientation q
    | Sum.inr d => D.toClosedOrientedManifold.orientation.orientation d := by
  intro x
  obtain ⟨hf, hfx⟩ := X.presentation_positive x
  rw [X.presentation_linearEquiv_eq x hf]
  exact hfx

structure SphericalCappingCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) where
  capping : DifferentialGeometry.Topology.SphericalCapping P.toClosedOrientedManifold
    N.toClosedOrientedManifold (SphericalTubeSystem.ofSmoothCutCapTransition X)
  coreInclusion_eq : ∀ x, capping.coreInclusion x = X.trace.capping.coreInclusion x

structure SmoothCutCapCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) extends SphericalCappingCompletion X where
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core, ∃ q : Q.Carrier,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q ∧
        ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : DifferentialGeometry.Topology.ClosedCell 3,
        X.presentation (toSphericalCappingCompletion.capping.cap b z) = Sum.inl q}
  presentation_positive :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.toClosedOrientedManifold.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.toClosedOrientedManifold.orientation.orientation q
    | Sum.inr d => D.toClosedOrientedManifold.orientation.orientation d

def SphericalCutCapTransition.ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    DifferentialGeometry.Topology.SphericalCutCapTransition P.toClosedOrientedManifold
      Q.toClosedOrientedManifold where
  source_nonempty := X.source_nonempty
  tubes := SphericalTubeSystem.ofSmoothCutCapTransition X
  capped := N.toClosedOrientedManifold
  capping := h.capping
  discarded := D.toClosedOrientedManifold
  presentation := X.presentation
  presentation_positive := fun x => by
    convert h.presentation_positive x using 2 <;>
      first
        | rfl
        | (cases X.presentation x <;> rfl)
  every_component_meets_core := h.every_component_meets_core
  retained_complement := h.retained_complement
  nontrivial := X.trace.nontrivial

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_tubes
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).tubes = SphericalTubeSystem.ofSmoothCutCapTransition X := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_presentation
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    ((SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = X.presentation := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).capping.coreInclusion x = X.trace.capping.coreInclusion x :=
  h.coreInclusion_eq x

theorem SphericalCutCapTransition.retainedCore_iff {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    x ∈ (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).retainedCore ↔ x ∈ X.trace.retainedCore := by
  rw [DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore,
    SphericalCutCapTransition.ofSmoothCutCapTransition_presentation]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq] at hq
      exact hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq]
      exact hq⟩

def ObservedHistory.toSurgeryFiniteSurgeryHistory (H : ObservedHistory.{u})
    (hn : 0 < H.eventCount)
    (hev : (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc).toClosedOrientedManifold
        (H.stage i.succ).toClosedOrientedManifold
        (H.time i.castSucc) (H.time i.succ))
    (hev_initial : ∀ i : Fin H.eventCount,
      (hev i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc)
    (hev_output : ∀ i : Fin H.eventCount,
      (hev i).outputMetric = H.initialMetric i.succ) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u} where
  eventCount := H.eventCount
  eventCount_pos := hn
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  stage := fun i => (H.stage i).toClosedOrientedManifold
  initialMetric := fun i => H.initialMetric i
  event := hev
  event_initial := hev_initial
  event_output := hev_output

def sumInlRange (Q D : Type*) [TopologicalSpace Q] [TopologicalSpace D] :
    TopologicalSpace.Opens (Q ⊕ D) :=
  ⟨range (Sum.inl : Q → Q ⊕ D), Topology.IsOpenEmbedding.inl.isOpen_range⟩

def sumInlCorestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : sumInlRange Q D :=
  ⟨Sum.inl q, ⟨q, rfl⟩⟩

theorem sumInlCorestrict_val {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : ((sumInlCorestrict (D := D) q : sumInlRange Q D) : Q ⊕ D) = Sum.inl q := rfl

noncomputable def sumInlRangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : Q := Classical.choose u.2

theorem sumInlRangeInv_spec {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : Sum.inl (sumInlRangeInv u) = u.1 := Classical.choose_spec u.2

theorem sumInlRangeInv_corestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (q : Q) : sumInlRangeInv (sumInlCorestrict (D := D) q) = q :=
  Sum.inl_injective (by rw [sumInlRangeInv_spec]; rfl)

theorem sumInlCorestrict_rangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D]
    (u : sumInlRange Q D) : sumInlCorestrict (D := D) (sumInlRangeInv u) = u :=
  Subtype.ext (sumInlRangeInv_spec u)

theorem continuous_sumInlRangeInv {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D] :
    Continuous (sumInlRangeInv (Q := Q) (D := D)) := by
  refine (Topology.IsEmbedding.inl (X := Q) (Y := D)).continuous_iff.mpr ?_
  have h : (Sum.inl ∘ sumInlRangeInv (Q := Q) (D := D)) =
      (Subtype.val : sumInlRange Q D → Q ⊕ D) :=
    funext fun u => sumInlRangeInv_spec u
  rw [h]
  exact continuous_subtype_val

theorem contMDiff_sumInlRangeInv {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (sumInlRangeInv (Q := Q) (D := D)) := by
  intro u
  have hφ : IsImmersionAt (𝓡 3) (𝓡 3) ∞ (Sum.inl : Q → Q ⊕ D) (sumInlRangeInv u) :=
    IsImmersion.isImmersionAt
      (IsImmersionOfComplement.sumInl (I := 𝓡 3) (M := Q) (M' := D)).isImmersion _
  rw [ContMDiffAt.iff_comp_isImmersionAt hφ]
  refine ⟨continuous_sumInlRangeInv.continuousAt, ?_⟩
  have h : (Sum.inl ∘ sumInlRangeInv (Q := Q) (D := D)) =
      (Subtype.val : sumInlRange Q D → Q ⊕ D) :=
    funext fun u => sumInlRangeInv_spec u
  rw [h]
  exact contMDiff_subtype_val.contMDiffAt

theorem continuous_sumInlCorestrict {Q D : Type*} [TopologicalSpace Q] [TopologicalSpace D] :
    Continuous (sumInlCorestrict (Q := Q) (D := D)) := by
  refine Topology.IsEmbedding.subtypeVal.continuous_iff.mpr ?_
  have h : (Subtype.val ∘ sumInlCorestrict (Q := Q) (D := D)) = (Sum.inl : Q → Q ⊕ D) :=
    funext fun q => sumInlCorestrict_val q
  rw [h]
  exact continuous_inl

theorem contMDiff_sumInlCorestrict {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (sumInlCorestrict (Q := Q) (D := D)) := by
  intro q
  have hφ : IsImmersionAt (𝓡 3) (𝓡 3) ∞
      (Subtype.val : sumInlRange Q D → Q ⊕ D) (sumInlCorestrict q) :=
    IsImmersion.isImmersionAt (IsImmersion.of_opens (sumInlRange Q D)) _
  rw [ContMDiffAt.iff_comp_isImmersionAt hφ]
  refine ⟨continuous_sumInlCorestrict.continuousAt, ?_⟩
  have h : (Subtype.val ∘ sumInlCorestrict (Q := Q) (D := D)) = (Sum.inl : Q → Q ⊕ D) :=
    funext fun q => sumInlCorestrict_val q
  rw [h]
  exact (IsSmoothEmbedding.sumInl (I := 𝓡 3) (M := Q) (M' := D)).contMDiff.contMDiffAt

noncomputable def sumInlRangeDiffeomorph {Q D : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D] :
    Diffeomorph (𝓡 3) (𝓡 3) (sumInlRange Q D) Q ∞ where
  toEquiv :=
    { toFun := sumInlRangeInv
      invFun := sumInlCorestrict
      left_inv := fun u => sumInlCorestrict_rangeInv u
      right_inv := fun q => sumInlRangeInv_corestrict q }
  contMDiff_toFun := contMDiff_sumInlRangeInv
  contMDiff_invFun := contMDiff_sumInlCorestrict

theorem isSmoothEmbedding_of_comp_sumInl {M Q D : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q] [TopologicalSpace D]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D]
    (f : M → Q) (h : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ ((Sum.inl : Q → Q ⊕ D) ∘ f)) :
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f := by
  let f' : M → sumInlRange Q D := fun x => sumInlCorestrict (Q := Q) (D := D) (f x)
  have hval : (Subtype.val ∘ f') = ((Sum.inl : Q → Q ⊕ D) ∘ f) := rfl
  have hf' : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
      (𝓡∂ 3) (𝓡 3) (sumInlRange Q D) f' (by rw [hval]; exact h)
  have hout := hf'.diffeomorph_comp (sumInlRangeDiffeomorph (Q := Q) (D := D))
  convert hout using 1
  funext x
  exact (sumInlRangeInv_corestrict (Q := Q) (D := D) (f x)).symm

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_poincareControlled
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : SmoothCutCapCompletion X)
    (hD : ∀ c : ConnectedComponents D.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        (D.toClosedOrientedManifold.component c).Carrier) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition X h).poincareControlled := hD

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem surgeryPresentation_coreInclusion (E : MetricCutCapEvent P Q a s)
    (hc : SmoothCutCapCompletion E.transition) (x : E.old) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).presentation
        ((SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).capping.coreInclusion
          x.1) =
      Sum.inl (E.oldOutput x) := by
  rw [SphericalCutCapTransition.ofSmoothCutCapTransition_presentation,
    SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion,
    E.transition.presentation_eq, E.oldOutput_eq]
  rfl

theorem surgeryRetainedCore (E : MetricCutCapEvent P Q a s) (hc : SmoothCutCapCompletion E.transition) :
    E.old ⊆ (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).retainedCore :=
  fun _ hx =>
    (SphericalCutCapTransition.retainedCore_iff E.transition hc _).mpr (E.old_retained hx)

theorem surgeryContainsOutside (E : MetricCutCapEvent P Q a s) (hc : SmoothCutCapCompletion E.transition)
    (x : (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).tubes.core)
    (hx : x ∈
      (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).retainedCore)
    (hnot : x.1 ∉
      (SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc).tubes.surgeryRegion) :
    x ∈ (E.old : Set ↑(SphericalCutCapTransition.ofSmoothCutCapTransition E.transition
      hc).tubes.core) :=
  E.old_contains_outside x
    ((SphericalCutCapTransition.retainedCore_iff E.transition hc x).mp hx)
    (fun i hi => hnot (Set.mem_iUnion.mpr ⟨i, hi⟩))

noncomputable def toSurgery (E : MetricCutCapEvent P Q a s)
    (hc : SmoothCutCapCompletion E.transition)
    (hout : letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : E.old => E.transition.trace.capping.coreInclusion x.1)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
      P.toClosedOrientedManifold Q.toClosedOrientedManifold a s := by
  letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  letI : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  exact
  { transition := SphericalCutCapTransition.ofSmoothCutCapTransition E.transition hc
    incoming := E.incoming.toSurgery
    terminal := E.terminal.toSurgery
    outputMetric := E.outputMetric
    unchanged := E.old
    unchanged_compact := E.old_compact
    unchanged_retained := surgeryRetainedCore E hc
    unchangedCharts := E.oldCharts
    unchangedSmooth := E.oldSmooth
    unchanged_induced := E.old_induced
    terminalInclusion := E.oldTerminal
    terminalInclusion_eq := E.oldTerminal_eq
    terminalInclusion_smooth := by
      refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 3) ThreeModel
        _ E.oldTerminal ?_
      convert E.old_induced using 1
      funext x
      exact E.oldTerminal_eq x
    outputInclusion := E.oldOutput
    outputInclusion_eq := surgeryPresentation_coreInclusion E hc
    outputInclusion_smooth := by
      have hG : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
          (fun x : E.old =>
            E.transition.presentation (E.transition.trace.capping.coreInclusion x.1)) :=
        hout.diffeomorph_comp E.transition.presentation
      have hG' : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
          ((Sum.inl : Q.Carrier → Q.Carrier ⊕ E.discarded.Carrier) ∘
            (fun x : E.old => E.oldOutput x)) := by
        convert hG using 1
        funext x
        rw [Function.comp_apply, E.transition.presentation_eq, E.oldOutput_eq]
      exact isSmoothEmbedding_of_comp_sumInl (fun x : E.old => E.oldOutput x) hG'
    unchanged_metric_eq := E.old_metric_eq
    unchanged_contains_outside := surgeryContainsOutside E hc
    every_component_meets_unchanged := E.every_child_meets_old }

end MetricCutCapEvent

namespace ObservedHistory

variable (H : ObservedHistory.{u})

noncomputable def toSurgeryEvents
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1)) :
    (i : Fin H.eventCount) →
      DifferentialGeometry.PDE.RicciFlow.Surgery.MetricCutCapEvent
        (H.stage i.castSucc).toClosedOrientedManifold
        (H.stage i.succ).toClosedOrientedManifold
        (H.time i.castSucc) (H.time i.succ) :=
  fun i => MetricCutCapEvent.toSurgery (H.event i) (hc i) (hout i)

theorem toSurgeryEvents_initial
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (i : Fin H.eventCount) :
    ((H.toSurgeryEvents hc hout) i).incoming.flow.base.metric (H.time i.castSucc) =
      H.initialMetric i.castSucc :=
  H.event_initial i

theorem toSurgeryEvents_output
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1))
    (i : Fin H.eventCount) :
    ((H.toSurgeryEvents hc hout) i).outputMetric = H.initialMetric i.succ :=
  H.event_output i

noncomputable def toSurgeryFiniteSurgeryHistory_of_cutCapCompletion (H : ObservedHistory.{u})
    (hn : 0 < H.eventCount)
    (hc : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (hout : (i : Fin H.eventCount) →
      letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : (H.event i).old => (H.event i).transition.trace.capping.coreInclusion x.1)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u} :=
  H.toSurgeryFiniteSurgeryHistory hn (H.toSurgeryEvents hc hout)
    (H.toSurgeryEvents_initial hc hout) (H.toSurgeryEvents_output hc hout)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
