import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRetainedBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRetainedSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRetainedInterior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreSeparatedWidth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRadialSquare

/-!
The same actual regular-fibre complements assemble a raw presentation retaining every old seam.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private def radialBoundaryTori {C : CompactCarrier.{u}}
    (Γ : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hs : Γ.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (Γ (t, halfZero))) : BoundaryTori C 1 where
  collar := Fin.cases Γ (fun j => j.elim0)
  source_eq j := by fin_cases j; exact hs
  boundary_zero j t := by fin_cases j; exact hb t
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim

private theorem radialBoundaryTori_image {C : CompactCarrier.{u}}
    (Γ : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hs : Γ.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (Γ (t, halfZero))) :
    (radialBoundaryTori Γ hs hb).image = range (fun t => Γ (t, halfZero)) := by
  ext x
  simp only [BoundaryTori.image, mem_iUnion]
  constructor
  · rintro ⟨j, t, ht⟩
    fin_cases j
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨0, t, ht⟩

namespace RawGraphPresentation

variable {M : ConnectedClosedOrientedManifold.{u} 3}
variable (G : RawGraphPresentation (NoCuts.carrier M))
variable (i : Fin G.components.count)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)
variable (hUi : φ.target ⊆ G.components.piece i)
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : IsSmoothEmbedding K.model G.cutCarrier.model ∞ ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (hbij : ∀ x, Bijective (mfderiv K.model G.cutCarrier.model ι x))
variable (ho : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective K.model G.cutCarrier.model ι hbij x).toLinearEquiv
  (K.orientation.orientation x) = G.cutCarrier.orientation.orientation (ι x))
variable (ΓK : PartialDiffeomorph halfCollarModel K.model
  (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
variable (hΓKs : ΓK.source = halfCollarSource)
variable (hΓKb : ∀ t, K.model.IsBoundaryPoint (ΓK (t, halfZero)))
variable (hΓK : ∀ p, p ∈ halfCollarSource →
  ι (ΓK p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (hbK : ι '' K.model.boundary K.Carrier =
  G.cutCarrier.model.boundary G.cutCarrier.Carrier ∪
    range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)))
variable (O : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hOt : O.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hO : ∀ x, x ∈ O.source → ι (O x) = x)
variable (D : K.Components) (H : ∀ j, CircleFibration K (D.piece j))
variable (hc : D.count = G.components.count)
variable (hm : ∀ (j : Fin G.components.count) (x : K.Carrier),
  x ∈ D.piece (Fin.cast hc.symm j) ↔ ι x ∈ G.components.piece j)
variable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
variable (hleft : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆ O.source)
variable (hright : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆ O.source)
variable (haL : ∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (haR : ∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
  (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ)
variable (L : CompactCarrier.{u}) (η : L.Carrier → M.Carrier)
variable (hη : IsSmoothEmbedding L.model (NoCuts.carrier M).model ∞ η)
variable (hηbij : ∀ x, Bijective (mfderiv L.model (NoCuts.carrier M).model η x))
variable (hηo : ∀ x, Orientation.map (Fin 3)
  (Manifold.differentialEquivOfBijective L.model (NoCuts.carrier M).model η hηbij x).toLinearEquiv
  (L.orientation.orientation x) = M.orientation.orientation (η x))
variable (ΓL : PartialDiffeomorph halfCollarModel L.model
  (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
variable (hΓLs : ΓL.source = halfCollarSource)
variable (hΓLb : ∀ t, L.model.IsBoundaryPoint (ΓL (t, halfZero)))
variable (hΓL : ∀ p, p ∈ halfCollarSource →
  η (ΓL p) = G.transportRegularFibreTube φ h3 hI
    (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (hbL : η '' L.model.boundary L.Carrier =
  (NoCuts.carrier M).model.boundary M.Carrier ∪
    range (fun t : Torus => G.transportRegularFibreTube φ h3 hI
      (ULift.up (t.1 : ℂ), t.2)))
variable (O_L : PartialDiffeomorph (NoCuts.carrier M).model L.model
  M.Carrier L.Carrier ∞)
variable (hO_Ls : O_L.source = ((G.transportRegularFibreTube φ h3 hI) ''
  {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hO_L : ∀ x, x ∈ O_L.source → η (O_L x) = x)
variable (ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι.isEmbedding hrange).setoid
  ≃ₜ L.Carrier)
variable (hρ : ∀ x : K.Carrier,
  η (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)))

def fibreExcisionRawPresentation : RawGraphPresentation L := by
  let P := G.fibreRetainedPairing φ h3 hI K ι hι.isEmbedding hrange hι.contMDiff hbij ho
    O hO hδ hδ1 hleft hright
  let V := G.fibreRetainedInteriorImage φ h3 hI K O L O_L
  let e := G.fibreRetainedInteriorDiffeomorph φ h3 hI K ι hι.isEmbedding hrange hbK
    O hOs hOt L O_L hO_Ls
  let EK := radialBoundaryTori ΓK hΓKs hΓKb
  let EL := radialBoundaryTori ΓL hΓLs hΓLb
  refine
    { cutCarrier := K
      components := D
      fibration := H
      pairing := P
      externalCount := 1
      external := EL
      cutExternal := EK
      external_exhausted := ?_
      cut_boundary_exhausted := ?_
      external_disjoint := ?_
      reconstruction := ρ
      quotient_smooth := ?_
      quotient_oriented := ?_
      interiorImage := V
      interiorDiffeomorph := e
      interior_map := ?_
      seam := G.fibreRetainedSeam L O_L hδ
      seam_source := ?_
      seam_zero := ?_
      seam_positive := ?_
      seam_negative := ?_
      seam_interior := G.fibreRetainedSeam_interior hδ L O_L
      seam_disjoint := G.fibreRetainedSeam_disjoint hδ L O_L
      marked_collar := ?_
      external_seam_disjoint := ?_
      leftPiece j := Fin.cast hc.symm (G.leftPiece j)
      rightPiece j := Fin.cast hc.symm (G.rightPiece j)
      left_owned := ?_
      right_owned := ?_
      externalPiece := Fin.cases (Fin.cast hc.symm i) (fun j => j.elim0)
      external_owned := ?_ }
  · rw [radialBoundaryTori_image]
    exact G.fibreAmbientRadialBoundary_exhausted φ h3 hI L η hη.isEmbedding ΓL hΓL hbL
  · rw [radialBoundaryTori_image]
    exact G.fibreRetainedBoundary_exhausted φ h3 hI K ι hι.isEmbedding hrange ΓK hΓK hbK
  · rw [radialBoundaryTori_image]
    exact G.fibreRetainedBoundary_disjoint φ h3 hI K ι hι.isEmbedding hrange ΓK hΓK
  · exact G.fibreRetainedFold_contMDiff φ h3 hI hδ hδ1 K O hleft hright L
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη ρ hρ
  · exact G.fibreRetainedFold_oriented φ h3 hI hδ hδ1 K O hleft hright L
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hηbij hηo ρ hρ
  · intro x
    exact G.fibreRetainedInteriorPD_apply φ h3 hI K ι hι.isEmbedding hrange O hO L η
      hη.isEmbedding O_L hO_L ρ hρ x.val (by
        rw [G.fibreRetainedInteriorPD_source φ h3 hI K ι hι.isEmbedding hrange hbK O
          hOs hOt L O_L hO_Ls]
        exact x.property)
  · exact G.fibreRetainedSeam_source φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
  · exact G.fibreRetainedSeam_zero φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · exact G.fibreRetainedSeam_positive φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · exact G.fibreRetainedSeam_negative φ h3 hI hδ hδ1 K O hOs hleft hright L O_L hO_Ls
      ι hι.isEmbedding hrange hι.contMDiff hbij ho hO η hη hO_L ρ hρ
  · intro j p hp
    fin_cases j
    exact G.fibreRetainedRadialSquare φ h3 hI K ι hι.isEmbedding hrange ΓK hΓK
      L η hη.isEmbedding.injective ΓL hΓL ρ hρ p hp
  · intro j c
    fin_cases j
    exact (G.fibreRetainedSeam_disjoint_radial φ h3 hI hδ hδ1 K O hOs hleft hright
      L O_L hO_Ls η hO_L haL haR ΓL hΓLs hΓL c).symm
  · intro j x hx
    apply (hm (G.leftPiece j) x).mpr
    exact G.left_owned j hx
  · intro j x hx
    apply (hm (G.rightPiece j) x).mpr
    exact G.right_owned j hx
  · intro j
    fin_cases j
    exact G.fibreRetainedBoundary_owned φ h3 K ι ΓK hΓK i hUi D hc hm

end RawGraphPresentation

end GC.GraphManifold
