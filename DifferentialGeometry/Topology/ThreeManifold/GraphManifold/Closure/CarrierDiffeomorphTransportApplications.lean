import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# Consumers of the carrier-diffeomorphism transport

Concrete uses of `exists_rawGraphPresentation_of_carrierDiffeomorph` and the model recognitions:
the orientation-reversed model carriers (an orientation-REVERSING identity, the branch the tree's
closed-manifold version could not reach for bounded carriers), and two successive transports.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

/-- The solid torus with the reversed orientation has a raw presentation with one piece, no
pairing torus and one external torus. -/
theorem exists_rawGraphPresentation_solidTorusCarrier_opposite :
    ∃ G : RawGraphPresentation solidTorusCarrier.{u}.opposite,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 :=
  exists_rawGraphPresentation_of_solidTorus_diffeomorph (W := solidTorusCarrier.{u}.opposite)
    (Diffeomorph.refl solidTorusCarrier.{u}.model solidTorusCarrier.{u}.Carrier ∞)

/-- The twisted interval bundle over the Klein bottle with the reversed orientation. -/
theorem exists_rawGraphPresentation_mobiusBundleCarrier_opposite :
    ∃ G : RawGraphPresentation mobiusBundleCarrier.{u}.opposite,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 :=
  exists_rawGraphPresentation_of_twistedIBundle_diffeomorph (W := mobiusBundleCarrier.{u}.opposite)
    (Diffeomorph.refl mobiusBundleCarrier.{u}.model mobiusBundleCarrier.{u}.Carrier ∞)

/-- `T² × I` with the reversed orientation: its two external tori are the boundary tori of the
annulus presentation, point by point. -/
theorem exists_rawGraphPresentation_annulusCircleCarrier_opposite :
    ∃ G : RawGraphPresentation annulusCircleCarrier.{u}.opposite,
      ∃ h : G.externalCount = annulusRawPresentation.{u}.externalCount,
        G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 2 ∧
        ∀ i t, G.external.torusMap i t =
          annulusRawPresentation.{u}.external.torusMap (Fin.cast h i) t :=
  exists_rawGraphPresentation_of_torusProduct_diffeomorph (W := annulusCircleCarrier.{u}.opposite)
    (Diffeomorph.refl annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier ∞)

/-- Two successive transports: a raw presentation of a preconnected carrier moves along a
composite of two carrier diffeomorphisms, with the external tori moved by the composite. -/
theorem exists_rawGraphPresentation_of_carrierDiffeomorph_trans {W W' W'' : CompactCarrier.{u}}
    [PreconnectedSpace W.Carrier] (G : RawGraphPresentation W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (e' : W'.Carrier ≃ₘ⟮W'.model, W''.model⟯ W''.Carrier) :
    ∃ G'' : RawGraphPresentation W'', ∃ h : G''.externalCount = G.externalCount,
      ∀ i t, G''.external.torusMap i t = e' (e (G.external.torusMap (Fin.cast h i) t)) := by
  have : PreconnectedSpace W'.Carrier := by
    refine ⟨?_⟩
    have h := (isPreconnected_univ (α := W.Carrier)).image e e.continuous.continuousOn
    rwa [image_univ, (show range e = univ from e.surjective.range_eq)] at h
  obtain ⟨G', h', -, -, ht'⟩ := exists_rawGraphPresentation_of_carrierDiffeomorph G e
  obtain ⟨G'', h'', -, -, ht''⟩ := exists_rawGraphPresentation_of_carrierDiffeomorph G' e'
  refine ⟨G'', h''.trans h', fun i t => ?_⟩
  rw [ht'', ht']
  rfl

end GC.GraphManifold
