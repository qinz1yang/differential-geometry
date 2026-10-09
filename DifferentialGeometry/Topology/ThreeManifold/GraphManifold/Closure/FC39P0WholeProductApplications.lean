import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0WholeProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalApplications

/-!
# FC39 producer, GROUP G-product (review 56, D56-5): consumers of the whole-product certificate

* `exists_labelled_presentation_of_wholeProduct` — the product branch of the boundary threshold: a
  carrier diffeomorphic to `annulus × S¹` with ANY nearly cuspidal boundary `B` has a raw graph
  presentation whose external tori are the components of `B` under a renumbering. It runs the FC42
  form-(b) consumer (`StrongCertificate.raw_or_aux_nonneg`) on the SAME strong certificate
  `wholeProductStrongCertificate B e` through `exists_boundary_presentation_of_rimProduct_of_consumer`
  (the closed alternative is excluded because `B` has a non-empty component).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- A carrier diffeomorphic to `annulus × S¹` is connected. -/
theorem connectedSpace_of_productDiffeomorph_GI
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ConnectedSpace W.Carrier :=
  e.toHomeomorph.connectedSpace_iff.mp (connectedSpace_productSet (Or.inl rfl))

/-- **Consumer: the labelled boundary presentation of a whole product**, from the FC42 form-(b)
consumer on the whole-product strong certificate. -/
theorem exists_labelled_presentation_of_wholeProduct {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ G : RawGraphPresentation W, ∃ σ : Fin B.count ≃ Fin G.externalCount,
      ∀ i, Set.range (G.external.torusMap (σ i)) = B.component i := by
  have := connectedSpace_of_productDiffeomorph_GI e
  exact exists_boundary_presentation_of_rimProduct_of_consumer
    (@fun W' _ _ _ D h => StrongCertificate.raw_or_aux_nonneg W' ⟨D, h⟩) W B
    (wholeProductStrongCertificate B e).1 (wholeProductStrongCertificate B e).2

end GC.GraphManifold.Assembly.FC39P0
