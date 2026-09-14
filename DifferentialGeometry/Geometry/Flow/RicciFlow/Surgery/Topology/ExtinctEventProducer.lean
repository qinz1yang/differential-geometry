import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTimeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctEventModelConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionFrontierSatisfiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmoothCutCapFrameReversing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeBallChartDictionary

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem OrientedThreeStage.exists_incomingSlab_terminalLimitMetric_of_metric
    (P : OrientedThreeStage.{u}) (g : P.Metric) (a : ℝ) :
    ∃ s : ℝ, a < s ∧ ∃ G : P.IncomingSlab a s,
      Nonempty G.TerminalLimitMetric ∧ G.flow.base.metric a = g := by
  obtain ⟨b, hab, S, hS⟩ := exists_closedSlab_of_metric P g a
  exact ⟨b, hab, S.restrictIncoming le_rfl S.lt le_rfl,
    ⟨OrientedThreeStage.ClosedSlab.endpointTerminalLimitMetric P S⟩, hS⟩

theorem OrientedThreeStage.exists_retainedCoreEvent_of_isEmpty_output_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) [IsEmpty Q.Carrier]
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation)
    (g : P.Metric) :
    ∃ (s : ℝ) (_ : 0 < s) (E : RetainedCoreEvent P Q 0 s),
      E.incoming.flow.base.metric 0 = g ∧ E.transition.boundaryFrameReversing ∧
        E.toMetricCutCapEvent.hasCutCapCompletion := by
  obtain ⟨s, hs, G, hL, hmet⟩ :=
    OrientedThreeStage.exists_incomingSlab_terminalLimitMetric_of_metric P g 0
  let E : RetainedCoreEvent P Q 0 s :=
    RetainedCoreEvent.ofEmptyOutput X G hL.some (OrientedThreeStage.metricOfIsEmpty Q)
  exact ⟨s, hs, E, hmet, X.boundaryFrameReversing_of_attaching_eq_refl h hout,
    E.toMetricCutCapEvent_hasCutCapCompletion_of_attaching_eq_refl h hout⟩

theorem hasExtinctRetainedCoreHistory_of_isEmpty_output_of_attaching_eq_refl
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    {Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q D N)
    [IsEmpty Q.Carrier]
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation)
    (hctrl : ∀ q : ConnectedComponents D.Carrier,
      DifferentialGeometry.Topology.isPoincareStandard
        (D.toClosedOrientedManifold.component q).Carrier) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨s, hs, G, hL, hmet⟩ :=
    OrientedThreeStage.exists_incomingSlab_terminalLimitMetric_of_metric
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g 0
  let E : RetainedCoreEvent
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q 0 s :=
    RetainedCoreEvent.ofEmptyOutput X G hL.some (OrientedThreeStage.metricOfIsEmpty Q)
  exact hasExtinctRetainedCoreHistory_of_extinctionEvent M g hs inferInstance E hmet
    (X.boundaryFrameReversing_of_attaching_eq_refl h hout) hctrl

theorem hasControlledExtinctionWithin_mono
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier} {B B' : ℝ} (hBB' : B ≤ B') :
    HasControlledExtinctionWithin M g B → HasControlledExtinctionWithin M g B' :=
  fun ⟨W, hW⟩ => ⟨W, hW.trans hBB'⟩

theorem exists_hasControlledExtinctionWithin_iff_nonempty
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    (∃ B : ℝ, HasControlledExtinctionWithin M g B) ↔
      Nonempty (PoincareControlledExtinction M g) :=
  ⟨fun ⟨_, h⟩ => nonempty_poincareControlledExtinction_of_hasControlledExtinctionWithin h,
    fun ⟨W⟩ => ⟨W.time, ⟨W, le_rfl⟩⟩⟩

theorem exists_pos_hasControlledExtinctionWithin_of_nonempty
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : Nonempty (PoincareControlledExtinction M g)) :
    ∃ B : ℝ, 0 < B ∧ HasControlledExtinctionWithin M g B :=
  h.elim fun W => ⟨W.time, W.time_pos, ⟨W, le_rfl⟩⟩

theorem hasControlledExtinctionWithin_pos
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier} {B : ℝ}
    (h : HasControlledExtinctionWithin M g B) : 0 < B :=
  lt_of_not_ge fun hB => not_hasControlledExtinctionWithin_of_nonpos hB h

theorem hasControlledExtinctionWithin_of_retainedCoreHistory_time
    {P : OrientedThreeStage.{u}} {g : P.Metric} (H : RetainedCoreHistory P)
    [Nonempty P.Carrier]
    (A : InitialIdentification P g H.toHistory)
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    HasControlledExtinctionWithin P.toClosedOrientedManifold g
      (H.time (Fin.last H.eventCount)) :=
  hasControlledExtinctionWithin_of_observedHistory P g H.toHistory A
    (fun i => ((H.coreEvent i).toMetricCutCapEvent_hasCutCapCompletion (hbfr i)).some)
    (fun i => (H.coreEvent i).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding)
    hctrl hempty le_rfl

namespace RetainedCoreEvent

theorem extinctionHistory_time_last {P Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s)
    (E : RetainedCoreEvent P Q 0 s) :
    (extinctionHistory hs E).time (Fin.last (extinctionHistory hs E).eventCount) = s := rfl

private def extinctionHistory_initial {P Q : OrientedThreeStage.{u}} {g : P.Metric}
    {s : ℝ} (hs : 0 < s) (E : RetainedCoreEvent P Q 0 s)
    (hm : E.incoming.flow.base.metric 0 = g) :
    InitialIdentification P g (extinctionHistory hs E).toHistory := by
  refine ⟨Diffeomorph.refl ThreeModel P.Carrier ∞,
    preservesTangentOrientation_refl P.orientation, ?_⟩
  intro x v w
  change (E.incoming.flow.base.metric 0).inner x
    (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x v)
    (mfderiv ThreeModel ThreeModel (id : P.Carrier → P.Carrier) x w) = g.inner x v w
  rw [mfderiv_id, hm]
  rfl

theorem hasControlledExtinctionWithin_of_extinctionEvent
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s) (hQ : IsEmpty Q.Carrier)
    (E : RetainedCoreEvent
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q 0 s)
    (hm : E.incoming.flow.base.metric 0 = g)
    (hbfr : E.transition.boundaryFrameReversing)
    (hctrl : E.toMetricCutCapEvent.poincareStandardDiscarded)
    {B : ℝ} (hB : s ≤ B) :
    HasControlledExtinctionWithin M.toClosedOrientedManifold g B := by
  refine hasControlledExtinctionWithin_mono (B := s) (B' := B) hB ?_
  refine @hasControlledExtinctionWithin_of_retainedCoreHistory_time
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g
    (extinctionHistory hs E) M.connected.toNonempty (extinctionHistory_initial hs E hm)
    (fun i => ?_) (fun i => ?_) ?_
  · fin_cases i
    exact hbfr
  · fin_cases i
    exact hctrl
  · rw [extinctionHistory_stage_last hs E]
    exact hQ

end RetainedCoreEvent

theorem OrientedThreeStage.ClosedSlab.not_singularEndpoint {P : OrientedThreeStage.{u}}
    {u v : ℝ} (G : P.ClosedSlab u v) :
    ¬ (G.restrictIncoming le_rfl G.lt le_rfl).SingularEndpoint :=
  fun h => OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint _
    h (G.terminalRegularRegion_eq_univ P)

attribute [local instance] threeBallChartedSpace threeBall_isManifold

private abbrev standardNeckFrameEquiv
    (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0))
    (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0)) :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ]
      TangentSpace ThreeModel (standardNeckCapping.cap standardNeckBoundaryFalse 0) :=
  (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
    (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj)

private abbrev standardNeckAmbientDeriv :
    TangentSpace (𝓡 3) (standardNeckCapFun false 0) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓡 3) (𝓡 4) (fun y : Sphere 3 => (y : EuclideanSpace ℝ (Fin 4)))
    (standardNeckCapFun false 0)

private theorem standardNeckCapBoundaryFrame_not_pos
    (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0))
    (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0)) :
    ¬ 0 < sphereOutwardDeterminant 3 (standardNeckCapFun false 0)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map (standardNeckFrameEquiv hi hj)) := by
  rw [sphereOutwardDeterminant_eq_basisDet_frame]
  have hfun : (fun j : Fin 4 => Fin.cases (standardNeckCapFun false 0)
        (fun k : Fin 3 => standardNeckAmbientDeriv
          (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
            (standardNeckFrameEquiv hi hj)) k)) j)
      = (Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
          (Fin.cons (standardNeckAmbientDeriv
              ((standardNeckFrameEquiv hi hj) (standardNeckCapChartVector 0)))
            (Fin.cons (standardNeckAmbientDeriv
                ((standardNeckFrameEquiv hi hj) (standardNeckCapChartVector 1)))
              (Fin.cons (standardNeckAmbientDeriv
                  ((standardNeckFrameEquiv hi hj) (standardNeckCapChartVector 2)))
                ![])))) := by
    funext j
    induction j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Fin.cons_zero, standardNeckCapFun_false_zero_val]
    | succ i =>
      simp only [Fin.cases_succ, Fin.cons_succ]
      induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, OrthonormalBasis.coe_toBasis, Module.Basis.map_apply,
          EuclideanSpace.basisFun_apply, standardNeckCapChartVector_eq_single]
      | succ k =>
        simp only [Fin.cons_succ]
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, OrthonormalBasis.coe_toBasis, Module.Basis.map_apply,
            EuclideanSpace.basisFun_apply, standardNeckCapChartVector_eq_single,
            Fin.succ_zero_eq_one]
        | succ l =>
          simp only [Fin.cons_succ]
          induction l using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero, OrthonormalBasis.coe_toBasis, Module.Basis.map_apply,
              EuclideanSpace.basisFun_apply, standardNeckCapChartVector_eq_single,
              Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
          | succ m => exact Fin.elim0 m
  intro h
  exact standardNeckCapDictionaryFrame_det_not_pos hi hj (hfun ▸ h)

theorem not_nonempty_standardNeckCutCapInputs : ¬ Nonempty StandardNeckCutCapInputs :=
  not_nonempty_standardNeckCutCapInputs_of_capFrameDeterminant_not_pos
    fun hi hj => standardNeckCapBoundaryFrame_not_pos hi hj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
