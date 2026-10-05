import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcisionRaw

/-!
The same physical fibre excision retains its connected carrier and literal one-port radial collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem connected_of_single_raw_component {K : CompactCarrier.{u}}
    (G : RawGraphPresentation K) (hc : G.components.count = 1) : ConnectedSpace K.Carrier := by
  let i : Fin G.components.count := ⟨0, by omega⟩
  let : ConnectedSpace (G.components.piece i) := G.components.connected i
  have hs : Surjective (Subtype.val : G.components.piece i → G.cutCarrier.Carrier) := by
    intro x
    have hx : x ∈ ⋃ j, (G.components.piece j : Set G.cutCarrier.Carrier) := by
      rw [G.components.covers]
      trivial
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hji : j = i := Fin.ext (by have hjb := j.isLt; have hib := i.isLt; omega)
    exact ⟨⟨x, hji ▸ hj⟩, rfl⟩
  let : ConnectedSpace G.cutCarrier.Carrier := hs.connectedSpace continuous_subtype_val
  have hq : Surjective (G.reconstruction ∘ G.pairing.quotientMap) :=
    G.reconstruction.surjective.comp Quotient.mk_surjective
  exact hq.connectedSpace (G.reconstruction.continuous.comp G.pairing.quotientMap.continuous)

private theorem onePort_cast_collar {K : CompactCarrier.{u}} {n : ℕ}
    (Γ : BoundaryTori K n) (hn : n = 1) (i : Fin 1) :
    (hn ▸ Γ : BoundaryTori K 1).collar i = Γ.collar (Fin.cast hn.symm i) := by
  subst n
  rfl

private theorem onePort_cast_image {K : CompactCarrier.{u}} {n : ℕ}
    (Γ : BoundaryTori K n) (hn : n = 1) : (hn ▸ Γ : BoundaryTori K 1).image = Γ.image := by
  subst n
  rfl

theorem exists_fibredExcisionConnectedData
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CircleFibration (NoCuts.carrier M) ⊤) :
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
        (PlaneLift.{u} × Circle) M.Carrier ∞,
    {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧
    ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
      (G : RawGraphPresentation K),
      K.kind = .withBoundary ∧
      IsSmoothEmbedding K.model (𝓡 3) ∞ ι ∧
      range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Function.Bijective (mfderiv K.model (𝓡 3) ι x)) ∧
      (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
        D.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
          M.orientation.orientation (ι x)) ∧
      G.components.count = 1 ∧ G.pairing.count = 0 ∧
      ∃ hcount : G.externalCount = 1,
      (∀ (i : Fin G.externalCount) (p : Torus × EuclideanHalfSpace 1),
        p ∈ halfCollarSource →
        ι (G.external.collar i p) =
          φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      ConnectedSpace K.Carrier ∧
      ∃ Γ : BoundaryTori K 1,
        (∀ i : Fin 1, Γ.collar i = G.external.collar (Fin.cast hcount.symm i)) ∧
        K.model.boundary K.Carrier = Γ.image ∧
        ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
          ι (Γ.collar 0 p) =
            φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  obtain ⟨φ, h3, K, ι, G, hK, hι, hr, hbij, hO, hc, hp, hn, hrad⟩ :=
    exists_fibredExcisionRaw M F
  let Γ : BoundaryTori K 1 := hn ▸ G.external
  have hcollar : ∀ i : Fin 1, Γ.collar i = G.external.collar (Fin.cast hn.symm i) :=
    onePort_cast_collar G.external hn
  have hb : K.model.boundary K.Carrier = Γ.image :=
    G.external_exhausted.trans (onePort_cast_image G.external hn).symm
  refine ⟨φ, h3, K, ι, G, hK, hι, hr, hbij, hO, hc, hp, hn, hrad,
    connected_of_single_raw_component G hc, Γ, hcollar, hb, ?_⟩
  intro p hps
  rw [hcollar]
  exact hrad (Fin.cast hn.symm 0) p hps

end GC.GraphManifold
