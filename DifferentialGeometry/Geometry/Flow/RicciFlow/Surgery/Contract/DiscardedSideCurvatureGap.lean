import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.DiscardedSideGeometry
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature (admitsConstantPositiveSectionalCurvature
  constantPositiveSectionalCurvatureMetric)

universe u

private theorem componentMap_cancel
    {D D' : ClosedOrientedManifold.{u} 3} (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (C : ConnectedComponents D.Carrier) :
    e.1.symm.continuous.connectedComponentsMap (e.1.continuous.connectedComponentsMap C) = C := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [Continuous.connectedComponentsMap_mk e.1.continuous x,
    Continuous.connectedComponentsMap_mk e.1.symm.continuous (e.1 x),
    Diffeomorph.symm_apply_apply]

private theorem componentMap_mem
    {D D' : ClosedOrientedManifold.{u} 3} (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (C : ConnectedComponents D.Carrier) (x : (D.component C).Carrier) :
    ConnectedComponents.mk (e.1 x.1) = e.1.continuous.connectedComponentsMap C :=
  congrArg e.1.continuous.connectedComponentsMap x.2

private theorem componentMap_inv_mem
    {D D' : ClosedOrientedManifold.{u} 3} (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (C : ConnectedComponents D.Carrier)
    (y : (D'.component (e.1.continuous.connectedComponentsMap C)).Carrier) :
    ConnectedComponents.mk (e.1.symm y.1) = C :=
  (congrArg e.1.symm.continuous.connectedComponentsMap y.2).trans (componentMap_cancel e C)

private noncomputable def componentDiffeomorph
    {D D' : ClosedOrientedManifold.{u} 3} (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (C : ConnectedComponents D.Carrier) :
    (D.component C).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯
      (D'.component (e.1.continuous.connectedComponentsMap C)).Carrier where
  toEquiv :=
    { toFun := fun x => ⟨e.1 x.1, componentMap_mem e C x⟩
      invFun := fun y => ⟨e.1.symm y.1, componentMap_inv_mem e C y⟩
      left_inv := fun x => Subtype.ext (e.1.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.1.apply_symm_apply y.1) }
  contMDiff_toFun := by
    intro x
    exact codRestr_contMDiffAt (V := D'.componentOpen (e.1.continuous.connectedComponentsMap C))
      (componentMap_mem e C) ((e.1.contMDiff.comp contMDiff_subtype_val).contMDiffAt)
  contMDiff_invFun := by
    intro y
    exact codRestr_contMDiffAt (V := D.componentOpen C)
      (componentMap_inv_mem e C) ((e.1.symm.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

theorem admitsConstantPositiveSectionalCurvature_component_of_orientedDiffeomorph
    {D D' : ClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (C : ConnectedComponents D.Carrier)
    (h : admitsConstantPositiveSectionalCurvature
      (I := ThreeModel) (M := (D.component C).Carrier)) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel)
      (M := (D'.component (e.1.continuous.connectedComponentsMap C)).Carrier) :=
  admitsConstantPositiveSectionalCurvature_of_diffeomorph
    (M := D'.component (e.1.continuous.connectedComponentsMap C)) (N := D.component C)
    (componentDiffeomorph e C).symm h

theorem admitsConstantPositiveSectionalCurvature_componentwise_of_orientedDiffeomorph
    {D D' : ClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph D D')
    (h : ∀ C : ConnectedComponents D.Carrier,
      admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := (D.component C).Carrier))
    (C' : ConnectedComponents D'.Carrier) :
    admitsConstantPositiveSectionalCurvature
      (I := ThreeModel) (M := (D'.component C').Carrier) := by
  obtain ⟨C, rfl⟩ := Continuous.connectedComponentsMap_surjective e.1.continuous
    (fun y => ⟨e.1.symm y, e.1.apply_symm_apply y⟩) C'
  exact admitsConstantPositiveSectionalCurvature_component_of_orientedDiffeomorph e C (h C)

theorem admitsConstantPositiveSectionalCurvature_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold)
    (h : admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := N.Carrier)) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) :=
  admitsConstantPositiveSectionalCurvature_of_diffeomorph (M := M) (N := N) e.1 h

theorem admitsConstantPositiveSectionalCurvature_of_orientedDiffeomorph_trans
    {M N L : ConnectedClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold)
    (f : ClosedOrientedManifold.OrientedDiffeomorph N.toClosedOrientedManifold
      L.toClosedOrientedManifold)
    (h : admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := L.Carrier)) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) :=
  admitsConstantPositiveSectionalCurvature_of_orientedDiffeomorph
    (M := M) (N := L) (e.trans f) h

theorem isStandardFactor_of_constantPositiveSectionalCurvature
    {M : ConnectedClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric ThreeModel M.Carrier}
    (hg : constantPositiveSectionalCurvatureMetric g) : isStandardFactor M :=
  isStandardFactor_of_admitsConstantPositiveSectionalCurvature (M := M) ⟨g, hg⟩

theorem isStandardFactor_component_of_discardedComponentsRoundOrSphereProduct
    (D : ClosedOrientedManifold.{u} 3) (h : DiscardedComponentsRoundOrSphereProduct D)
    (C : ConnectedComponents D.Carrier) : isStandardFactor (D.component C) :=
  (h C).elim
    (fun hp => isStandardFactor_of_admitsConstantPositiveSectionalCurvature (M := D.component C) hp)
    isStandardFactor_of_isSphereTwoTimesCircleFactor

theorem componentwiseStandardFactor_of_discardedComponentsRoundOrSphereProduct
    (D : ClosedOrientedManifold.{u} 3) (h : DiscardedComponentsRoundOrSphereProduct D) :
    D.componentwiseStandardFactor :=
  D.componentwiseStandardFactor_iff.mpr
    fun C => isStandardFactor_component_of_discardedComponentsRoundOrSphereProduct D h C

theorem SphericalCutCapTransition.poincareControlled_of_discardedComponentsRoundOrSphereProduct
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (h : DiscardedComponentsRoundOrSphereProduct E.discarded) : E.poincareControlled :=
  E.poincareControlled_of_componentwiseConnectedSumStandardFactor
    (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor E.discarded
      (componentwiseStandardFactor_of_discardedComponentsRoundOrSphereProduct E.discarded h))

theorem RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseDiscardedGeometry
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)
    (h : T.discardedSideGeometry) : T.hasPoincareStandardDiscarded :=
  fun n j =>
    MetricCutCapEvent.poincareStandardDiscarded_of_discardedComponentsRoundOrSphereProduct
      _ (h n j)

theorem ClosedOrientedManifold.disjoint_componentSet_of_ne (D : ClosedOrientedManifold.{u} 3)
    {C C' : ConnectedComponents D.Carrier} (h : C ≠ C') :
    Disjoint (D.componentSet C) (D.componentSet C') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact h ((D.mem_componentSet C x).mp hx |>.symm.trans ((D.mem_componentSet C' x).mp hx'))

theorem MetricCutCapEvent.finite_discardedComponents {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) : Finite (ConnectedComponents E.discarded.Carrier) :=
  ClosedOrientedManifold.finite_components E.discarded.toClosedOrientedManifold

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
