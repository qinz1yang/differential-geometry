import DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNormalization
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCorePuncturedFrontier

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def RfsHurewiczFrontier (M : Type u) [TopologicalSpace M] : Prop :=
  Subsingleton (DifferentialGeometry.Topology.integralSingularHomology 2 M) ∧
    DifferentialGeometry.Topology.SphereHurewiczTwoCanonical M ∧
      DifferentialGeometry.Topology.SphereHurewiczThreeCanonical M

def cubeSphereCollapseClassIsUnit : Prop :=
  DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
    DifferentialGeometry.Topology.cubeSphereFundamentalClass.{u}

def squareSphereCollapseClassIsUnit : Prop :=
  DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1
    DifferentialGeometry.Topology.squareSphereFundamentalClass.{u}

open DifferentialGeometry.Topology in
theorem squareSphereCollapseClassIsUnit_iff_exists_relativeFunctional :
    squareSphereCollapseClassIsUnit.{u} ↔
      ∃ ψ : DifferentialGeometry.Topology.integralRelativeHomology 2
          DifferentialGeometry.Topology.liftedSphereBasepoint.{u} →ₗ[ℤ] ℤ,
        ψ (DifferentialGeometry.Topology.integralAbsoluteToRelative 2
          DifferentialGeometry.Topology.liftedSphereBasepoint.{u}
          DifferentialGeometry.Topology.squareSphereFundamentalClass.{u}) = 1 :=
  squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional

theorem exists_isSphereHomologyGenerator_one_liftedHomotopySphere :
    ∃ c : DifferentialGeometry.Topology.integralSingularHomology 2
        (DifferentialGeometry.Topology.liftedHomotopySphere.{u} 1),
      DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1 c :=
  ⟨DifferentialGeometry.Topology.integralLiftedSphereGenerator.{u} 1,
    DifferentialGeometry.Topology.integralLiftedSphereGenerator_isGenerator 1⟩

variable {M : Type u} [TopologicalSpace M]

theorem subsingleton_homotopyGroup_two_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) :
    ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) :=
  fun q => (DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2).1

theorem bijective_hurewiczThree_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (q : M) :
    Function.Bijective (hurewiczThree q) :=
  (DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2).2

theorem nonempty_mulEquiv_homotopyGroup_three_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (q : M) :
    Nonempty (HomotopyGroup (Fin 3) M q ≃* Multiplicative (IntegralHomology M 3)) :=
  ⟨MulEquiv.ofBijective (hurewiczThreeHom q)
    (bijective_hurewiczThree_of_hurewiczFrontier h hdeg q)⟩

theorem rfsHurewiczFrontier_of_lowDegreeFrontier
    (h : DifferentialGeometry.Topology.HurewiczLowDegreeFrontier M)
    (hH₂ : Subsingleton (DifferentialGeometry.Topology.integralSingularHomology 2 M)) :
    RfsHurewiczFrontier M :=
  ⟨hH₂, h.1, h.2⟩

theorem rfsHurewiczFrontier_punit : RfsHurewiczFrontier PUnit.{u + 1} :=
  ⟨DifferentialGeometry.Topology.integralSingularHomology_subsingleton_of_contractible 2
      (by norm_num) PUnit.{u + 1},
    DifferentialGeometry.Topology.hurewiczLowDegreeFrontier_punit.1,
    DifferentialGeometry.Topology.hurewiczLowDegreeFrontier_punit.2⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem rfs_homotopy_groups_of_hurewiczFrontier (h : RfsHurewiczFrontier M)
    (hdeg : cubeSphereCollapseClassIsUnit.{u}) (o : TangentOrientationSection M) (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  let _ := o
  exact DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q h.1 hdeg h.2.1 h.2.2

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def ChildSimplicityFrontier (E : SmoothCutCapTransition P Q D N) : Prop :=
  E.childCollaredStarCoverProducer ∧ E.ComponentwisePuncturedCoreOfParent

theorem child_simplyConnected_of_childSimplicityFrontier (E : SmoothCutCapTransition P Q D N)
    (h : ChildSimplicityFrontier E) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_puncturedCoreProducer h.1 h.2 c

theorem childSimplicityFrontier_of_isEmpty_childCapBoundary
    (E : SmoothCutCapTransition P Q D N)
    [∀ c : ConnectedComponents Q.Carrier, IsEmpty (E.ChildCapBoundary c)]
    (hcore : E.ChildCoreSimplyConnected) : ChildSimplicityFrontier E :=
  ⟨fun c _ => E.nonempty_childCarrierCollaredStarCover_of_isEmpty_childCapBoundary c,
    (E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mpr
      (E.childCoreSimplyConnectedOfParent_of_childCoreSimplyConnected hcore)⟩

theorem childSimplicityFrontier_of_childCoreSimplyConnected
    (E : SmoothCutCapTransition P Q D N) (hcover : E.childCollaredStarCoverProducer)
    (hcore : E.ChildCoreSimplyConnected) : ChildSimplicityFrontier E :=
  ⟨hcover,
    (E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mpr
      (E.childCoreSimplyConnectedOfParent_of_childCoreSimplyConnected hcore)⟩

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
