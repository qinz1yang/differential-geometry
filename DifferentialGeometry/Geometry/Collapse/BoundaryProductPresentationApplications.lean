import DifferentialGeometry.Geometry.Collapse.BoundaryProductPresentation

/-!
# Consumers of the BCF04 whole-product case

`exists_boundary_graph_conclusion_of_product` is the conclusion of the admitted
`exists_boundary_graph_threshold` (`Geometry/Collapse/GraphManifold.lean:144–147`), verbatim,
for every member in BCP03's whole-product alternative. `isEmpty_torusProduct_diffeomorph_of_count`
is the contrapositive count: a nearly cuspidal boundary with a number of components other than
two excludes the product alternative.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Geometry.Collapse

/-- The labelled conclusion of `exists_boundary_graph_threshold`, verbatim, in the whole-product
case. -/
theorem exists_boundary_graph_conclusion_of_product {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W,
      ∃ e : Fin B.count ≃ Fin G.externalCount,
        ∀ i, Set.range (G.external.torusMap (e i)) = B.component i := by
  obtain ⟨G, -, -, -, he⟩ := exists_boundary_presentation_of_product B e
  exact ⟨G, he⟩

/-- A nearly cuspidal boundary whose number of components is not two excludes BCP03's
whole-product alternative. -/
theorem isEmpty_torusProduct_diffeomorph_of_count {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hB : B.count ≠ 2) :
    IsEmpty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯
      W.Carrier) :=
  ⟨fun e => hB (B.count_eq_two_of_torusProduct e)⟩

end DifferentialGeometry.Geometry.Collapse
