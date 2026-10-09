import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairingTopology
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcisionWithBoundary

/-!
The same actual transported fibre tube determines an ambient compact complement and the whole
retained gluing quotient homeomorphism, preserving every excision field and reconstruction square.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (L : CompactCarrier.{u}) (jL : L.Carrier → W.Carrier)
variable (hjL : _root_.Topology.IsEmbedding jL)
variable (hL : range jL = G.FibreAmbientComplement φ h3 hI)

def fibreAmbientComplementHomeomorph : L.Carrier ≃ₜ G.FibreAmbientComplement φ h3 hI := by
  let f : L.Carrier → G.FibreAmbientComplement φ h3 hI := fun x =>
    ⟨jL x, hL ▸ mem_range_self x⟩
  have hf : Bijective f := by
    constructor
    · intro x y he
      exact hjL.injective (congrArg Subtype.val he)
    · intro y
      have hy : y.val ∈ range jL := by rw [hL]; exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    (hjL.continuous.subtype_mk _)

theorem fibreAmbientComplementHomeomorph_apply (x : L.Carrier) :
    (G.fibreAmbientComplementHomeomorph φ h3 hI L jL hjL hL x).val = jL x := rfl

theorem fibreAmbientComplementHomeomorph_symm_apply (y : G.FibreAmbientComplement φ h3 hI) :
    jL ((G.fibreAmbientComplementHomeomorph φ h3 hI L jL hjL hL).symm y) = y.val := by
  have he := congrArg Subtype.val
    ((G.fibreAmbientComplementHomeomorph φ h3 hI L jL hjL hL).apply_symm_apply y)
  rw [G.fibreAmbientComplementHomeomorph_apply] at he
  exact he

variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)

def fibreAmbientRetainedHomeomorph :
    Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid ≃ₜ L.Carrier :=
  (G.fibreRetainedQuotientHomeomorph φ h3 hI K ι hι hrange).trans
    (G.fibreAmbientComplementHomeomorph φ h3 hI L jL hjL hL).symm

theorem fibreAmbientRetainedHomeomorph_apply (x : K.Carrier) :
    jL (G.fibreAmbientRetainedHomeomorph φ h3 hI L jL hjL hL K ι hι hrange
      (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)) := by
  change jL ((G.fibreAmbientComplementHomeomorph φ h3 hI L jL hjL hL).symm
    (G.fibreRetainedQuotientHomeomorph φ h3 hI K ι hι hrange (Quotient.mk'' x))) = _
  exact (G.fibreAmbientComplementHomeomorph_symm_apply φ h3 hI L jL hjL hL
    (G.fibreRetainedQuotientHomeomorph φ h3 hI K ι hι hrange (Quotient.mk'' x))).trans
      (G.fibreRetainedQuotientHomeomorph_apply φ h3 hI K ι hι hrange x)

theorem exists_rawFibreAmbient
    {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
      (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
    (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ G.cutCarrier.interior) :
    let ψ := G.transportRegularFibreTube φ h3 hI
    ∃ (L : CompactCarrier.{u}) (jL : L.Carrier → W.Carrier)
      (Γ : PartialDiffeomorph halfCollarModel L.model
        (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
      (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞),
      L.kind = .withBoundary ∧
      IsSmoothEmbedding L.model W.model ∞ jL ∧
      range jL = (ψ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Function.Bijective (mfderiv L.model W.model jL x)) ∧
      (∀ x, ∃ D : TangentSpace L.model x ≃L[ℝ] TangentSpace W.model (jL x),
        D.toContinuousLinearMap = mfderiv L.model W.model jL x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (L.orientation.orientation x) =
          W.orientation.orientation (jL x)) ∧
      Γ.source = halfCollarSource ∧
      (∀ t, L.model.IsBoundaryPoint (Γ (t, halfZero))) ∧
      (∀ p, p ∈ halfCollarSource →
        jL (Γ p) = ψ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      jL '' L.model.boundary L.Carrier = W.model.boundary W.Carrier ∪
        range (fun t : Torus => ψ (ULift.up (t.1 : ℂ), t.2)) ∧
      Disjoint (W.model.boundary W.Carrier)
        (range (fun t : Torus => ψ (ULift.up (t.1 : ℂ), t.2))) ∧
      O_L.source = (ψ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
      (∀ x, x ∈ O_L.source → jL (O_L x) = x) ∧
      O_L.target = jL ⁻¹' (ψ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
      ∀ (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
        (hι : _root_.Topology.IsEmbedding ι)
        (hrange : range ι = G.FibreCutComplement φ),
        ∃ ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid ≃ₜ L.Carrier,
          ∀ x : K.Carrier,
            jL (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)) := by
  let ψ := G.transportRegularFibreTube φ h3 hI
  obtain ⟨L, jL, Γ, O_L, hkind, hemb, hr, hbij, hpositive, hΓ, hzero, hradial,
    hboundary, hdisjoint, hOsource, hOidentity, hOtarget⟩ :=
    CircleFibration.exists_fibreExcisionWithBoundary W ψ
      (G.transportRegularFibreTube_closedRadius φ h3 hI)
  refine ⟨L, jL, Γ, O_L, hkind, hemb, hr, hbij, hpositive, hΓ, hzero, hradial,
    hboundary, hdisjoint, hOsource, hOidentity, hOtarget, ?_⟩
  intro K ι hι hrange
  exact ⟨G.fibreAmbientRetainedHomeomorph φ h3 hI L jL hemb.isEmbedding hr K ι hι hrange,
    G.fibreAmbientRetainedHomeomorph_apply φ h3 hI L jL hemb.isEmbedding hr K ι hι hrange⟩

end GC.GraphManifold.RawGraphPresentation
