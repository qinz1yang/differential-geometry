import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature (admitsConstantPositiveSectionalCurvature)

def DiscardedComponentsRoundOrSphereProduct (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier,
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := (D.component C).Carrier) ∨
      isSphereTwoTimesCircleFactor (D.component C)

theorem componentwisePositiveCurvatureOrSphereProduct_of_discardedComponentsRoundOrSphereProduct
    (D : ClosedOrientedManifold.{u} 3) (h : DiscardedComponentsRoundOrSphereProduct D) :
    componentwisePositiveCurvatureOrSphereProduct D := by
  intro C
  rcases h C with hp | hcy
  · exact ⟨[D.component C], fun F hF => by
      rw [List.mem_singleton] at hF
      subst hF
      exact Or.inl hp, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  · exact ⟨[D.component C], fun F hF => by
      rw [List.mem_singleton] at hF
      subst hF
      exact Or.inr hcy, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem MetricCutCapEvent.poincareStandardDiscarded_of_discardedComponentsRoundOrSphereProduct
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : DiscardedComponentsRoundOrSphereProduct E.discarded.toClosedOrientedManifold) :
    E.poincareStandardDiscarded :=
  MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    E
    (componentwisePositiveCurvatureOrSphereProduct_of_discardedComponentsRoundOrSphereProduct
      E.discarded.toClosedOrientedManifold h)

def RetainedCoreObservationTower.discardedSideGeometry {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : RetainedCoreObservationTower P g) : Prop :=
  ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
    DiscardedComponentsRoundOrSphereProduct
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold

theorem RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_discardedSideGeometry
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)
    (h : T.discardedSideGeometry) : T.hasPoincareStandardDiscarded :=
  fun n j => MetricCutCapEvent.poincareStandardDiscarded_of_discardedComponentsRoundOrSphereProduct
    _ (h n j)

theorem discardedComponentsRoundOrSphereProduct_standardThreeSphereLift :
    DiscardedComponentsRoundOrSphereProduct
      standardThreeSphereLift.{u}.toClosedOrientedManifold := by
  intro C
  exact Or.inl (admitsConstantPositiveSectionalCurvature_of_diffeomorph
    (M := standardThreeSphereLift.toClosedOrientedManifold.component C)
    (N := standardThreeSphereLift)
    ((standardThreeSphereLift.toClosedOrientedManifold.componentOrientedDiffeomorph C).1)
    admitsConstantPositiveSectionalCurvature_standardThreeSphereLift)

theorem discardedComponentsRoundOrSphereProduct_sphereTwoTimesCircleLift :
    DiscardedComponentsRoundOrSphereProduct
      sphereTwoTimesCircleLift.toClosedOrientedManifold := by
  intro C
  exact Or.inr (isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
    ⟨sphereTwoTimesCircleLift.toClosedOrientedManifold.componentOrientedDiffeomorph C⟩
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift)

theorem discardedSideGeometry_empty (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).discardedSideGeometry :=
  fun n j => Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_discardedSideGeometry
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (h : T.discardedSideGeometry)
    (hextinct : towerExtinct T.toObservationTower) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap M g T hbfr
    (T.hasPoincareStandardDiscarded_of_discardedSideGeometry h) hextinct

end DifferentialGeometry.PDE.RicciFlow.Surgery
