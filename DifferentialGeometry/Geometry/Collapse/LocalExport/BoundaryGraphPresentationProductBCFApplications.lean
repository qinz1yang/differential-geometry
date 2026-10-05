import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationProductBCF
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0WholeProductApplications

/-!
# Consumer of BCF04's whole-product branch (lane B-BCF134)

`exists_rawGraphPresentation_of_product_BCF04`: the certificate of
`boundary_graphPresentation_of_product_BCF04` fed to FC42 form (b)
(`StrongCertificate.raw_or_aux_nonneg` through
`exists_boundary_presentation_of_rimProduct_of_consumer`) gives a raw graph presentation whose
external tori are the packet's labelled cusp components.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
open GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **Consumer (FC42 form (b))**: in the whole-product branch the carrier has a raw graph
presentation whose external tori are the packet's cusp components, with a bijection of labels. -/
theorem exists_rawGraphPresentation_of_product_BCF04 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b
    s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) :
    ∃ G : RawGraphPresentation W, ∃ σ : Fin S.packet.cusp.count ≃ Fin G.externalCount,
      ∀ i, range (G.external.torusMap (σ i)) = S.packet.cusp.component i := by
  obtain ⟨_, ⟨⟨D, hD⟩⟩, -⟩ := boundary_graphPresentation_of_product_BCF04 S h
  exact exists_boundary_presentation_of_rimProduct_of_consumer
    (@fun W' _ _ _ D' h' => FC39P0.StrongCertificate.raw_or_aux_nonneg W' ⟨D', h'⟩) W
    S.packet.cusp D hD

end DifferentialGeometry.Geometry.Collapse
