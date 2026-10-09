import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareStandardDiscarded
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature (admitsConstantPositiveSectionalCurvature)
open DifferentialGeometry.Topology (ClosedOrientedManifold ConnectedClosedOrientedManifold
  finiteConnectedSum isSphereTwoTimesCircleFactor isStandardFactor
  isStandardFactor_of_isSphereTwoTimesCircleFactor)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry in
theorem isStandardFactor_of_admitsConstantPositiveSectionalCurvature
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (hM : admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier)) :
    isStandardFactor M :=
  hM.elim fun g hg => Or.inl
    (exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature
      M g hg)

def componentwisePositiveCurvatureOrSphereProduct (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier, ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := F.Carrier) ∨
      isSphereTwoTimesCircleFactor F) ∧
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (D.component C).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold)

theorem componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct
    {D : ClosedOrientedManifold.{u} 3}
    (h : componentwisePositiveCurvatureOrSphereProduct D) :
    D.componentwiseConnectedSumStandardFactor := by
  intro C
  obtain ⟨L, hL, hdiff⟩ := h C
  exact ⟨L, fun F hF => (hL F hF).elim
    (fun hp => isStandardFactor_of_admitsConstantPositiveSectionalCurvature (M := F) hp)
    (fun hs => isStandardFactor_of_isSphereTwoTimesCircleFactor hs), hdiff⟩

theorem MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : componentwisePositiveCurvatureOrSphereProduct E.discarded.toClosedOrientedManifold) :
    E.poincareStandardDiscarded :=
  MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor E
    (componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct h)

namespace RetainedCoreObservationTower

theorem hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold) :
    T.hasPoincareStandardDiscarded :=
  hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor T
    fun n j =>
      componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct
        (h n j)

end RetainedCoreObservationTower

theorem
  exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct
    (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : RetainedCoreObservationTower P g, T.hasBoundaryFrameReversing ∧
      T.hasPoincareStandardDiscarded ∧ towerExtinct T.toObservationTower := by
  refine ⟨RetainedCoreObservationTower.empty P g, ?_, ?_,
    RetainedCoreObservationTower.towerExtinct_empty P g⟩
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold)
    (hextinct : towerExtinct T.toObservationTower) :
    hasCoreCompatibleObservationTower M g :=
  hasCoreCompatibleObservationTower_of_retainedCoreTower_cutCap M g T hbfr
    (T.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct h) hextinct

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold)
    (hextinct : towerExtinct T.toObservationTower) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap M g T hbfr
    (T.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct h) hextinct

end DifferentialGeometry.PDE.RicciFlow.Surgery
