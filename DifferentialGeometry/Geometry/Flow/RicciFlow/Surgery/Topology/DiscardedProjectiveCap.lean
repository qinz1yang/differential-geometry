import DifferentialGeometry.Topology.ThreeManifold.ProjectiveCapGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapModelTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

set_option autoImplicit false
noncomputable section
open Set Metric Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u
private abbrev S3 := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_discardedCap_model_collar_of_projective_cap_cover
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    [IsManifold ThreeModel ∞ Z] [T2Space Z] [CompactSpace Z]
    (pr : Perelman.CanonicalNeighborhood.FiniteHorn.ProjectivePresentation Z)
    (component : ConnectedComponents D.Carrier)
    (b : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace Z ∞)
    (F : PartialDiffeomorph ThreeModel ThreeModel Z
      (D.toClosedOrientedManifold.component component).Carrier ∞)
    (B : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
      (D.toClosedOrientedManifold.component component).Carrier ∞)
    (hb : closedBall (0 : ThreeSpace) 1 ⊆ b.source)
    (hF : (b '' ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source)
    (hB : closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (hcover : B '' closedBall (0 : ThreeSpace) 1 ∪ F '' (b '' ball (0 : ThreeSpace) 1)ᶜ = univ)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (hcomponent : ConnectedComponents.mk
      (E.trace.discardedCap boundary hdiscarded (0 : ThreeBall)) = component)
    (c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun z : Sphere 2 => E.trace.discardedCap boundary hdiscarded (sphereToThreeBall z)))
    (capSide : {q : Sphere 2 × symmetricOpenInterval c.radius // q.2.val ≤ 0} → ThreeBall)
    (hcap : ∀ q (hq : q.2.val ≤ 0),
      c.toFun q = E.trace.discardedCap boundary hdiscarded (capSide ⟨q,hq⟩)) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    (∃ (e : (D.toClosedOrientedManifold.component component).Carrier ≃ₘ⟮ThreeModel,ThreeModel⟯ S3)
      (a : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace S3 ∞)
      (fCap : C(ThreeBall,S3)) (profile : C(Sphere 2 × symmetricOpenInterval c.radius,S3)),
      a.source = univ ∧ IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ z : Sphere 2, (e.symm (fCap (sphereToThreeBall z))).val =
        E.trace.discardedCoreInclusion
          ⟨E.trace.tubes.coreBoundarySphere boundary (E.trace.capping.attaching boundary z),
            E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore boundary hdiscarded _⟩) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ profile ∧
      (∀ q, (e.symm (profile q)).val = c.toFun q) ∧
      (∀ q (hq : q.2.val ≤ 0), profile q = fCap (capSide ⟨q,hq⟩)) ∧
      ∃ U : Set (D.toClosedOrientedManifold.component component).Carrier,
        IsOpen U ∧ B '' closedBall (0 : ThreeSpace) 1 ⊆ U ∧
          U ⊆ (B.symm.trans a).source ∧ EqOn e (B.symm.trans a) U) ∨
    ∃ (e : (D.toClosedOrientedManifold.component component).Carrier ≃ₘ⟮ThreeModel,ThreeModel⟯ Z)
      (G : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace Z ∞)
      (R : ThreeSpace ≃ₘ[ℝ] ThreeSpace)
      (fCap : C(ThreeBall,Z)) (profile : C(Sphere 2 × symmetricOpenInterval c.radius,Z)),
      closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
      (G '' ball (0 : ThreeSpace) 1)ᶜ ⊆ F.source ∧
      R '' closedBall (0 : ThreeSpace) 1 = closedBall (0 : ThreeSpace) 1 ∧
      (∀ z ∈ closedBall (0 : ThreeSpace) 1, e (B (R z)) = G z) ∧
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ z : Sphere 2, (e.symm (fCap (sphereToThreeBall z))).val =
        E.trace.discardedCoreInclusion
          ⟨E.trace.tubes.coreBoundarySphere boundary (E.trace.capping.attaching boundary z),
            E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore boundary hdiscarded _⟩) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ profile ∧
      (∀ q, (e.symm (profile q)).val = c.toFun q) ∧
      (∀ q (hq : q.2.val ≤ 0), profile q = fCap (capSide ⟨q,hq⟩)) ∧
      EqOn e.symm F (G '' ball (0 : ThreeSpace) 1)ᶜ ∧
      e '' (B '' ball (0 : ThreeSpace) 1) = G '' ball (0 : ThreeSpace) 1 ∧
      ∃ U : Set Z, IsOpen U ∧ (G '' ball (0 : ThreeSpace) 1)ᶜ ⊆ U ∧
        U ⊆ F.source ∧ EqOn e.symm F U := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  have hp : IsLocalDiffeomorph ThreeModel ThreeModel ∞ pr.quotient :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      pr.quotient pr.smooth (fun x => (pr.local_diffeo x).injective) rfl
  obtain h | h := DifferentialGeometry.Topology.ThreeManifold.exists_sphere_or_projective_diffeomorph_of_cap_cover
    pr.quotient hp pr.onto pr.fibers b F B hb hF hB hcover
  · obtain ⟨e,a,ha,hBe,U,hU,hBU,hUs,hEq⟩ := h
    obtain ⟨fCap,profile,hf,hfe,hfb,hps,hpval,hpcap⟩ :=
      E.exists_discardedCap_model_collar_of_component_diffeomorph component e boundary hdiscarded hcomponent c capSide hcap
    exact Or.inl ⟨e,a,fCap,profile,ha,hf,hfe,hfb,hps,hpval,hpcap,U,hU,hBU,hUs,hEq⟩
  · obtain ⟨e,G,R,hG,hGF,hR,hBe,heF,heBall,hFc,hFs,U,hU,hGU,hUF,hEq⟩ := h
    obtain ⟨fCap,profile,hf,hfe,hfb,hps,hpval,hpcap⟩ :=
      E.exists_discardedCap_model_collar_of_component_diffeomorph component e boundary hdiscarded hcomponent c capSide hcap
    exact Or.inr ⟨e,G,R,fCap,profile,hG,hGF,hR,hBe,hf,hfe,hfb,hps,hpval,hpcap,heF,heBall,U,hU,hGU,hUF,hEq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
