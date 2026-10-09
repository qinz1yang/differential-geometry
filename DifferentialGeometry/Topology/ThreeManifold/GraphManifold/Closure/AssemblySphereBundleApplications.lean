import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereBundle

/-!
# Chapter-14 assembly, L3-S²: the raw presentation of an `S²`-bundle over the circle

Consumer of `AssemblySphereBundle.lean` (lane ASM-L3): the slim circle-base branch of the FC42
consumer for a sphere fibre (design §3, FC42 step 2). An oriented `S²`-bundle over the circle with
empty boundary has a raw graph presentation with one piece, no torus pairing and no external
torus (L3-S² followed by the `S² × S¹` adapter, with the counts of the transported presentation).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Counts

attribute [local instance] uliftChartedSpace isManifold_ulift

/-- The `S² × S¹` adapter with the counts of the presentation: one piece, no pairing, no external
torus. -/
theorem exists_rawGraphPresentation_counts_of_sphereTwoTimesCircle_diffeomorph
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (e : W.Carrier ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 0 := by
  let C := NoCuts.carrier sphereTwoTimesCircleLift.ulift.{0, u}
  let d : C.Carrier ≃ₘ⟮C.model, W.model⟯ W.Carrier :=
    (sphereTwoTimesCircleUliftProduct.{u}.trans
      ((uliftDiffeomorph (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.prodCongr
        sphereOneDiffeomorphCircle.symm)).trans e.symm
  have : PreconnectedSpace C.Carrier :=
    (d.toHomeomorph.connectedSpace_iff.mpr inferInstance).toPreconnectedSpace
  obtain ⟨G, h, hc, hp, -⟩ :=
    exists_rawGraphPresentation_of_carrierDiffeomorph sphereTwoTimesCircleUliftRawGraphPresentation.{u} d
  exact ⟨G, hc, hp, h⟩

end Counts

/-- **Slim circle-base branch, sphere fibre.** An oriented `S²`-bundle over the circle with empty
boundary has a raw graph presentation with one piece, no torus pairing and no external torus. -/
theorem exists_rawGraphPresentation_of_sphereBundle (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : ClosureSphere.{u} → W.Carrier) (hf : IsSmoothEmbedding (𝓡 2) W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 0 := by
  obtain ⟨e⟩ := exists_sphereTwoTimesCircle_of_sphereBundle W hW p hp hsub f hf hr
  exact exists_rawGraphPresentation_counts_of_sphereTwoTimesCircle_diffeomorph W e

end GC.GraphManifold.Assembly
