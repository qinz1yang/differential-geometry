import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BasicModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MobiusOnePiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate

/-!
# Raw presentations along diffeomorphisms of arbitrary carriers

`exists_rawGraphPresentation_of_carrierDiffeomorph`: a raw graph presentation of a compact
carrier `W` with preconnected underlying space moves along ANY smooth diffeomorphism
`W.Carrier ≃ₘ W'.Carrier` onto `W'`, whatever the two carrier models (closed or with boundary)
and whatever the orientations. The tree had this only for closed manifolds
(`rawGraphPresentation_of_diffeomorph`, `GraphManifold/Opposite.lean:163`). Proof: the
orientation dichotomy on a preconnected source (`GC.Seifert.preservesOrientation_or_opposite`)
and, in the reversing case, the presentation of the opposite carrier
(`RawGraphPresentation.opposite`) transported along the same map. The three counts are kept and
every external torus of the new presentation is the image of the corresponding old one.

Model recognitions on an arbitrary carrier `W` (chapter 14, FC42 / BCF04 inputs): a
diffeomorphism from the solid torus `solidTorusCarrier`, from the twisted interval bundle over
the Klein bottle `mobiusBundleCarrier`, or from `T² × I = annulusCircleCarrier` onto `W` gives a
raw presentation of `W` with one piece, no pairing torus, and one, one, two external tori.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

/-- **Transport of raw presentations along a diffeomorphism of arbitrary carriers.** The counts
are kept and every external torus of the new presentation is the image of the old one. -/
theorem exists_rawGraphPresentation_of_carrierDiffeomorph {W W' : CompactCarrier.{u}}
    [PreconnectedSpace W.Carrier] (G : RawGraphPresentation W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) :
    ∃ G' : RawGraphPresentation W', ∃ h : G'.externalCount = G.externalCount,
      G'.components.count = G.components.count ∧ G'.pairing.count = G.pairing.count ∧
      ∀ i t, G'.external.torusMap i t = e (G.external.torusMap (Fin.cast h i) t) := by
  rcases GC.Seifert.preservesOrientation_or_opposite e W.orientation W'.orientation with he | he
  · exact ⟨G.transport e he, rfl, rfl, rfl, fun _ _ => rfl⟩
  · exact ⟨G.opposite.transport (W := W.opposite) e he, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- `Nonempty` form of `exists_rawGraphPresentation_of_carrierDiffeomorph`. -/
theorem nonempty_rawGraphPresentation_of_carrierDiffeomorph {W W' : CompactCarrier.{u}}
    [PreconnectedSpace W.Carrier] (G : RawGraphPresentation W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) :
    Nonempty (RawGraphPresentation W') := by
  obtain ⟨G', -⟩ := exists_rawGraphPresentation_of_carrierDiffeomorph G e
  exact ⟨G'⟩

theorem solidTorusCarrier_connectedSpace : ConnectedSpace solidTorusCarrier.{u}.Carrier :=
  solidTorusDiscCircle.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem mobiusBundleCarrier_connectedSpace : ConnectedSpace mobiusBundleCarrier.{u}.Carrier :=
  mobiusRegularTotalCover_surjective.connectedSpace contMDiff_mobiusRegularTotalCover.continuous

theorem annulusCircleCarrier_connectedSpace : ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)

/-- **Solid torus recognition on `W`.** -/
theorem exists_rawGraphPresentation_of_solidTorus_diffeomorph {W : CompactCarrier.{u}}
    (e : solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 := by
  have := solidTorusCarrier_connectedSpace.{u}
  obtain ⟨G, h, hc, hp, -⟩ :=
    exists_rawGraphPresentation_of_carrierDiffeomorph solidTorusRawPresentation.{u} e
  obtain ⟨hc₀, hp₀, he₀⟩ := solidTorusRawPresentation_counts.{u}
  exact ⟨G, hc.trans hc₀, hp.trans hp₀, h.trans he₀⟩

/-- **Twisted interval bundle over the Klein bottle, recognition on `W`.** -/
theorem exists_rawGraphPresentation_of_twistedIBundle_diffeomorph {W : CompactCarrier.{u}}
    (e : mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 := by
  have := mobiusBundleCarrier_connectedSpace.{u}
  obtain ⟨G₀, hc₀, hp₀, he₀⟩ := exists_twistedIBundle_singlePieceRaw.{u}
  obtain ⟨G, h, hc, hp, -⟩ := exists_rawGraphPresentation_of_carrierDiffeomorph G₀ e
  exact ⟨G, hc.trans hc₀, hp.trans hp₀, h.trans he₀⟩

/-- **`T² × I` recognition on `W`.** The two external tori are the images of the two boundary
tori of the model. -/
theorem exists_rawGraphPresentation_of_torusProduct_diffeomorph {W : CompactCarrier.{u}}
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W, ∃ h : G.externalCount = annulusRawPresentation.{u}.externalCount,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 2 ∧
      ∀ i t, G.external.torusMap i t =
        e (annulusRawPresentation.{u}.external.torusMap (Fin.cast h i) t) := by
  have := annulusCircleCarrier_connectedSpace.{u}
  obtain ⟨G, h, hc, hp, ht⟩ :=
    exists_rawGraphPresentation_of_carrierDiffeomorph annulusRawPresentation.{u} e
  obtain ⟨hc₀, hp₀, he₀⟩ := annulusRawPresentation_counts.{u}
  exact ⟨G, h, hc.trans hc₀, hp.trans hp₀, h.trans he₀, ht⟩

end GC.GraphManifold
