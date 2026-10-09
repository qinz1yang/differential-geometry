import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibrePuncture

/-!
An arbitrary closed raw graph presentation supplies one actual connected physical fibre excision.
The same transported tube, raw puncture and one-port boundary collar are retained throughout.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem rawPhysicalOnePort_collar {K : CompactCarrier.{u}} {n : ℕ}
    (Γ : BoundaryTori K n) (he : n = 1) (i : Fin 1) :
    (he ▸ Γ : BoundaryTori K 1).collar i = Γ.collar (Fin.cast he.symm i) := by
  subst n
  rfl

private theorem rawPhysicalOnePort_image {K : CompactCarrier.{u}} {n : ℕ}
    (Γ : BoundaryTori K n) (he : n = 1) : (he ▸ Γ : BoundaryTori K 1).image = Γ.image := by
  subst n
  rfl

theorem exists_rawPhysicalExcisionData
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
        (PlaneLift.{u} × Circle) M.Carrier ∞,
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧
      ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
        (R : RawGraphPresentation K),
        K.kind = .withBoundary ∧
        ConnectedSpace K.Carrier ∧
        IsSmoothEmbedding K.model (𝓡 3) ∞ ι ∧
        range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
        (∀ x, Bijective (mfderiv K.model (𝓡 3) ι x)) ∧
        (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
          D.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
          Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
            M.orientation.orientation (ι x)) ∧
        ∃ (he : R.externalCount = 1) (Γ : BoundaryTori K 1),
          (∀ i : Fin 1, Γ.collar i = R.external.collar (Fin.cast he.symm i)) ∧
          K.model.boundary K.Carrier = Γ.image ∧
          ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
            ι (Γ.collar 0 p) =
              φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  have hs : Surjective (G.reconstruction ∘ G.pairing.quotientMap) :=
    G.reconstruction.surjective.comp Quotient.mk_surjective
  obtain ⟨x, hx⟩ := hs (Classical.arbitrary M.Carrier)
  have hcover : x ∈ ⋃ j, (G.components.piece j : Set G.cutCarrier.Carrier) := by
    rw [G.components.covers]
    trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  obtain ⟨ψ, h3, hI, K, ι, R, hUi, hK, hconn, hι, hr, hbij, hO,
    hc, hp, he, δ, hδ, hδ1, hmatching, hleft, hright, hexternal, hseam, hrad⟩ :=
    G.exists_connectedRawFibreExcision i
  let φ := G.transportRegularFibreTube ψ h3 hI
  let Γ : BoundaryTori K 1 := he ▸ R.external
  have hΓ : ∀ a : Fin 1, Γ.collar a = R.external.collar (Fin.cast he.symm a) :=
    rawPhysicalOnePort_collar R.external he
  have hb : K.model.boundary K.Carrier = Γ.image :=
    R.external_exhausted.trans (rawPhysicalOnePort_image R.external he).symm
  refine ⟨φ, G.transportRegularFibreTube_closedRadius ψ h3 hI,
    K, ι, R, hK, hconn, hι, hr, hbij, hO, he, Γ, hΓ, hb, ?_⟩
  intro p hps
  rw [hΓ]
  exact hrad p hps

end GC.GraphManifold
