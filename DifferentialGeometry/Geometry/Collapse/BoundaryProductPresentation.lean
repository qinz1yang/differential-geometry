import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# BCF04, whole-product case

BCF04 (B:9886–9966), first paragraph of its proof (B:9902): when the nearly cuspidal boundary
construction ends in BCP03's whole-product alternative (B:8323), the carrier is itself a circle
bundle over an annulus, and its labelled boundary identification gives the graph presentation.

`exists_boundary_presentation_of_product` takes BCP03's output, a smooth diffeomorphism from the
model `T² × I = annulusCircleCarrier` onto `W`, as DATA and returns a raw graph presentation of
the SAME `W` with one piece, no pairing torus and two external tori, together with the label
clause of `exists_boundary_graph_threshold` (`Geometry/Collapse/GraphManifold.lean:138`): the
external tori are the components of the nearly cuspidal boundary, matched by a bijection. The
label clause is `RawGraphPresentation.external_matching` (same file, :112). No connectedness
hypothesis is needed: the model is connected. Consequently such a boundary has exactly two
components.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Geometry.Collapse

/-- **BCF04, whole-product case.** BCP03's diffeomorphism `T² × I ≃ₘ W` as data gives the
labelled raw graph presentation of `W`. -/
theorem exists_boundary_presentation_of_product {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W,
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 2 ∧
      ∃ e' : Fin B.count ≃ Fin G.externalCount,
        ∀ i, Set.range (G.external.torusMap (e' i)) = B.component i := by
  obtain ⟨G, -, hc, hp, he, -⟩ := exists_rawGraphPresentation_of_torusProduct_diffeomorph e
  exact ⟨G, hc, hp, he, G.external_matching B⟩

/-- A nearly cuspidal boundary of a carrier diffeomorphic to `T² × I` has exactly two
components. -/
theorem NearlyCuspidalBoundary.count_eq_two_of_torusProduct {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    B.count = 2 := by
  obtain ⟨G, -, -, he, e', -⟩ := exists_boundary_presentation_of_product B e
  have h := Fintype.card_congr e'
  rw [Fintype.card_fin, Fintype.card_fin, he] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
