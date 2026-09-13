import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCoreCapCoverFrontier
import DifferentialGeometry.Topology.Manifold.SmoothBicollar
import DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge
import DifferentialGeometry.Topology.Embedding.Sphere

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

noncomputable def childSeamSphere (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    C(Sphere 2, E.ChildCarrier c) :=
  (E.childCoreInclusion c).comp (E.childCapSeam c b)

def seamSphereSmoothlyEmbedded (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Prop :=
  letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  IsSmoothEmbedding (𝓡 2) ThreeModel ∞ fun y : Sphere 2 => E.childSeamSphere c b y

theorem nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (h : E.seamSphereSmoothlyEmbedded c b) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
      (𝓡 2) ThreeModel fun y : Sphere 2 => E.childSeamSphere c b y) := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  exact DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (fun y : Sphere 2 => E.childSeamSphere c b y) h

theorem nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (h : E.seamSphereSmoothlyEmbedded c b) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      fun y : Sphere 2 => E.childSeamSphere c b y) := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  obtain ⟨h⟩ := E.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded c b h
  exact ⟨DifferentialGeometry.Topology.SmoothTwoSidedCollar.toTwoSidedCollar h⟩

theorem seamSphereSmoothlyEmbedded_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    ∀ b : E.ChildCapBoundary c, E.seamSphereSmoothlyEmbedded c b :=
  fun b => (IsEmpty.false b).elim

theorem simplyConnectedSpace_childCarrier_of_univ_V_producer
    (h : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        ∃ d : E.ChildCarrierCoreCapCover c, d.V = univ)
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (E.ChildCarrier c) := by
  obtain ⟨d, hd⟩ := h c inferInstance
  exact E.simplyConnectedSpace_childCarrier_of_cover_univ_V c d hd


def childCoreCapCoverAssembly : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      (∀ b : E.ChildCapBoundary c,
        Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
          fun y : Sphere 2 => E.childSeamSphere c b y)) →
        Nonempty (E.ChildCarrierCoreCapCover c)

theorem childCoreCapCoverProducer_of_seamCollarFrontier
    (hfrontier : ∀ (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c),
      E.seamSphereSmoothlyEmbedded c b)
    (hassembly : E.childCoreCapCoverAssembly) :
    E.childCoreCapCoverProducer := by
  intro c hpar
  exact hassembly c hpar fun b =>
    E.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded c b (hfrontier c b)

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

theorem nonempty_smoothTwoSidedCollar_roundSphere :
    Nonempty (SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
      (Subtype.val : SphereTwo → EuclideanSpace ℝ (Fin 3))) :=
  exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    (Subtype.val : SphereTwo → EuclideanSpace ℝ (Fin 3))
    (isSmoothEmbedding_coe_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2))

end DifferentialGeometry.Topology
