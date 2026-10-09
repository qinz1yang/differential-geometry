import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCoreCapCoverFrontier
import DifferentialGeometry.Topology.Manifold.SmoothBicollar
import DifferentialGeometry.Topology.VanKampen.SmoothTwoSidedCollarBridge
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

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

private theorem contMDiff_sphereToThreeBall :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
    ContMDiff (𝓡 2) (𝓡∂ 3) ∞ sphereToThreeBall := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  refine (ContMDiff.iff_comp_isImmersion E.ball_induced.isImmersion).mpr ?_
  exact ⟨sphereToThreeBall.continuous,
    (isSmoothEmbedding_coe_sphere (E := ThreeSpace) (n := 2)).contMDiff⟩

private theorem injective_mfderiv_sphereToThreeBall (x : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
    Function.Injective (mfderiv (𝓡 2) (𝓡∂ 3) sphereToThreeBall x) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have hinj := ((isSmoothEmbedding_coe_sphere (E := ThreeSpace) (n := 2)).isImmersion.isImmersionAt
    x).mfderiv_injective (by simp)
  have heq : (Subtype.val : Sphere 2 → ThreeSpace) =
      (Subtype.val : ThreeBall → ThreeSpace) ∘ sphereToThreeBall := rfl
  rw [heq, mfderiv_comp x (E.ball_induced.contMDiff.mdifferentiableAt (by simp))
    (E.contMDiff_sphereToThreeBall.mdifferentiableAt (by simp))] at hinj
  exact Function.Injective.of_comp hinj

private theorem capBoundary_isSmoothEmbedding (b : E.trace.tubes.Boundary) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (E.trace.capping.cap b ∘ sphereToThreeBall) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have hsm : ContMDiff (𝓡 2) ThreeModel ∞ (E.trace.capping.cap b ∘ sphereToThreeBall) :=
    (E.cap_smooth b).contMDiff.comp E.contMDiff_sphereToThreeBall
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) hsm ?_, ?_⟩
  · intro x
    rw [mfderiv_comp x ((E.cap_smooth b).contMDiff.mdifferentiableAt (by simp))
      (E.contMDiff_sphereToThreeBall.mdifferentiableAt (by simp))]
    exact ((E.cap_smooth b).isImmersion.isImmersionAt _).mfderiv_injective (by simp) |>.comp
      (E.injective_mfderiv_sphereToThreeBall x)
  · apply (E.cap_smooth b).isEmbedding.comp
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal

theorem childSeamSphere_isSmoothEmbedding (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) : E.seamSphereSmoothlyEmbedded c b := by
  let thisChart : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
  let thisSmooth : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
  let inclusion : E.ChildCarrier c → Q.Carrier ⊕ D.Carrier := fun q => Sum.inl q.1
  have heq : inclusion ∘ E.childSeamSphere c b =
      E.presentation ∘ (E.trace.capping.cap b.1 ∘ sphereToThreeBall) := by
    funext y
    change Sum.inl (E.childSeamSphere c b y).1 =
      E.presentation (E.trace.capping.cap b.1 (sphereToThreeBall y))
    rw [E.presentation_eq]
    exact (congrArg (fun q : E.ChildCarrier c => (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier))
      (E.childCap_boundary_eq c b y).symm).trans (E.childCapFun_eq c b _).symm
  have hcomp : IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (inclusion ∘ E.childSeamSphere c b) := by
    rw [heq]
    exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡 2) ThreeModel _ (E.capBoundary_isSmoothEmbedding b.1) E.presentation
  have hsm : ContMDiff (𝓡 2) ThreeModel ∞ (E.childSeamSphere c b) := by
    apply (ContMDiff.subtypeVal_comp_iff (Q.componentOpen c) _).mp
    exact contMDiff_of_contMDiff_inl hcomp.contMDiff
  have hi : ContMDiff ThreeModel ThreeModel ∞ inclusion :=
    ContMDiff.inl.comp (contMDiff_subtype_val (U := Q.componentOpen c))
  exact hcomp.of_comp (by simp) hsm hi

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

theorem nonempty_smoothTwoSidedCollar_childSeamSphere
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    letI : ChartedSpace ThreeSpace (E.ChildCarrier c) := (Q.component c).charts
    letI : IsManifold ThreeModel ∞ (E.ChildCarrier c) := (Q.component c).smooth
    Nonempty (DifferentialGeometry.Topology.SmoothTwoSidedCollar
      (𝓡 2) ThreeModel fun y : Sphere 2 => E.childSeamSphere c b y) :=
  E.nonempty_smoothTwoSidedCollar_of_seamSphereSmoothlyEmbedded c b
    (E.childSeamSphere_isSmoothEmbedding c b)

theorem nonempty_twoSidedCollar_childSeamSphere
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Nonempty (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      fun y : Sphere 2 => E.childSeamSphere c b y) :=
  E.nonempty_twoSidedCollar_of_seamSphereSmoothlyEmbedded c b
    (E.childSeamSphere_isSmoothEmbedding c b)

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


theorem childCoreCapCoverProducer_of_childCoreCapCoverAssembly
    (hassembly : E.childCoreCapCoverAssembly) : E.childCoreCapCoverProducer := by
  intro c hpar
  exact hassembly c hpar (E.nonempty_twoSidedCollar_childSeamSphere c)

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
