import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreAmbient

/-!
The same chosen radial collar is preserved by the actual retained quotient reconstruction.
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
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)
variable (ΓK : PartialDiffeomorph halfCollarModel K.model
  (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
variable (hΓK : ∀ p, p ∈ halfCollarSource →
  ι (ΓK p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (L : CompactCarrier.{u}) (η : L.Carrier → W.Carrier)
variable (hη : Injective η)
variable (ΓL : PartialDiffeomorph halfCollarModel L.model
  (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
variable (hΓL : ∀ p, p ∈ halfCollarSource →
  η (ΓL p) = G.transportRegularFibreTube φ h3 hI
    (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid ≃ₜ L.Carrier)
variable (hρ : ∀ x : K.Carrier,
  η (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)))

include hΓK hη hΓL hρ in
theorem fibreRetainedRadialSquare (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) : ρ (Quotient.mk'' (ΓK p)) = ΓL p := by
  apply hη
  rw [hρ, hΓK p hp, hΓL p hp]
  apply (G.transportRegularFibreTube_apply φ h3 hI _ ?_).symm
  apply h3
  change ‖(1 + p.2.val 0 / 2) • (p.1.1 : ℂ)‖ ≤ 3
  rw [norm_smul, Real.norm_of_nonneg (by linarith [p.2.property]), Circle.norm_coe, mul_one]
  change p.2.val 0 < 1 at hp
  linarith

end GC.GraphManifold.RawGraphPresentation
