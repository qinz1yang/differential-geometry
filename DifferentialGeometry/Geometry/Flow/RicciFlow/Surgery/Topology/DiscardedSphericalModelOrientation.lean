import DifferentialGeometry.Topology.ThreeManifold.SphericalModelOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapModelTransport

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u
variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_oriented_discardedCap_model_collar_of_spherical_diffeomorph
    (component : ConnectedComponents D.Carrier) (G : SphericalSpaceFormGroup)
    (e : (D.toClosedOrientedManifold.component component).Carrier
      ≃ₘ⟮ThreeModel, ThreeModel⟯ G.manifold.Carrier)
    (boundary : E.trace.tubes.Boundary) (hdiscarded : E.trace.capDiscarded boundary)
    (hcomponent : ConnectedComponents.mk
      (E.trace.discardedCap boundary hdiscarded (0 : ThreeBall)) = component)
    (c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun z : Sphere 2 => E.trace.discardedCap boundary hdiscarded (sphereToThreeBall z)))
    (capSide : {q : Sphere 2 × symmetricOpenInterval c.radius // q.2.val ≤ 0} → ThreeBall)
    (hcap : ∀ q (hq : q.2.val ≤ 0),
      c.toFun q = E.trace.discardedCap boundary hdiscarded (capSide ⟨q,hq⟩)) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∃ (H : SphericalSpaceFormGroup)
      (τ : G.manifold.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ H.manifold.Carrier)
      (f : ClosedOrientedManifold.OrientedDiffeomorph
        (D.toClosedOrientedManifold.component component).toClosedOrientedManifold H.manifold.toClosedOrientedManifold)
      (fCap : C(ThreeBall,G.manifold.Carrier))
      (profile : C(Sphere 2 × symmetricOpenInterval c.radius,G.manifold.Carrier))
      (fCap' : C(ThreeBall,H.manifold.Carrier))
      (profile' : C(Sphere 2 × symmetricOpenInterval c.radius,H.manifold.Carrier)),
      f.1 = e.trans τ ∧
      ((H = G ∧ HEq τ (Diffeomorph.refl ThreeModel G.manifold.Carrier ∞)) ∨
        τ.preservesOrientation G.manifold.orientation.opposite H.manifold.orientation) ∧
      (∀ x, fCap' x = τ (fCap x)) ∧ (∀ q, profile' q = τ (profile q)) ∧
      (∀ x : ThreeBall, (e.symm (fCap x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ q, (e.symm (profile q)).val = c.toFun q) ∧
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ fCap' ∧
      (∀ x : ThreeBall, (f.1.symm (fCap' x)).val = E.trace.discardedCap boundary hdiscarded x) ∧
      (∀ z : Sphere 2, (f.1.symm (fCap' (sphereToThreeBall z))).val =
        E.trace.discardedCoreInclusion
          ⟨E.trace.tubes.coreBoundarySphere boundary (E.trace.capping.attaching boundary z),
            E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore boundary hdiscarded _⟩) ∧
      ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ profile' ∧
      (∀ q, (f.1.symm (profile' q)).val = c.toFun q) ∧
      (∀ q (hq : q.2.val ≤ 0), profile' q = fCap' (capSide ⟨q,hq⟩)) ∧
      isStandardFactor (D.toClosedOrientedManifold.component component) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  obtain ⟨fCap,profile,hfCap,hfe,hfb,hps,hpe,hpc⟩ :=
    E.exists_discardedCap_model_collar_of_component_diffeomorph component e boundary hdiscarded hcomponent c capSide hcap
  obtain ⟨H,τ,f,hf,hτ,hstandard⟩ := exists_oriented_spherical_model_of_diffeomorph
    (D.toClosedOrientedManifold.component component) G e
  let fCap' : C(ThreeBall,H.manifold.Carrier) := ⟨τ ∘ fCap,τ.continuous.comp fCap.continuous⟩
  let profile' : C(Sphere 2 × symmetricOpenInterval c.radius,H.manifold.Carrier) :=
    ⟨τ ∘ profile,τ.continuous.comp profile.continuous⟩
  have hfc (x : G.manifold.Carrier) : f.1.symm (τ x) = e.symm x := by
    rw [hf]
    change e.symm (τ.symm (τ x)) = _
    rw [τ.symm_apply_apply]
  refine ⟨H,τ,f,fCap,profile,fCap',profile',hf,hτ,fun _ => rfl,fun _ => rfl,hfe,hpe,?_,?_,?_,
    τ.contMDiff.comp hps,?_,?_,hstandard⟩
  · exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡∂ 3) ThreeModel fCap hfCap τ
  · intro x
    exact (congrArg Subtype.val (hfc (fCap x))).trans (hfe x)
  · intro z
    exact (congrArg Subtype.val (hfc (fCap (sphereToThreeBall z)))).trans (hfb z)
  · intro q
    exact (congrArg Subtype.val (hfc (profile q))).trans (hpe q)
  · intro q hq
    exact congrArg τ (hpc q hq)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
