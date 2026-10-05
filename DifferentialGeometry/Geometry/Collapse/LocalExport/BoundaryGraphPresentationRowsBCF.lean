import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationProductBCFApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# BCF04, separated branch: the landing "rows ⟹ labelled certificate ⟹ labelled graph"
(lane B-BCF134; review 69 / lead 14:2x: G8 split)

Blueprint `master207B.tex`, BCF04 (B:9886–9965). Frozen G8 is split (dispositions-task69): the
rows producer `boundary_rows_of_actual_decomposition` (BIFACEc, frozen statement) and the general
landing proved here, with its true input — an FC39 row package `Rw : FC39RowsV2 W Et` on boundary
tori `Et` numbered by the packet's cusp components:

* `boundary_graphPresentation_of_rows_BCF04`: the conclusion of frozen G8 (`∃ Et`, a decomposition
  certificate with the rim-product clause, `range (Et.torusMap i) = S.packet.cusp.component i`),
  from FC39-G-FINAL's zero-argument landing `exists_strongCertificate_of_rows_GFIN`;
* `exists_rawGraphPresentation_of_rows_BCF04` (certificate ⟹ labelled graph): FC42 form (b) gives a
  raw graph presentation whose external tori are the packet's cusp components.
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

/-- **BCF04, the landing of the separated branch**: an FC39 row package on boundary tori numbered by
the packet's cusp components gives frozen G8's conclusion. -/
theorem boundary_graphPresentation_of_rows_BCF04 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    {Et : BoundaryTori W S.packet.cusp.count} (Rw : FC39P0.FC39RowsV2 W Et)
    (hEt : ∀ i, range (Et.torusMap i) = S.packet.cusp.component i) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i :=
  ⟨Et, FC39P0.exists_strongCertificate_of_rows_GFIN Rw, hEt⟩

/-- **Certificate ⟹ labelled graph** (FC42 form (b)) on the row package. -/
theorem exists_rawGraphPresentation_of_rows_BCF04 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    {Et : BoundaryTori W S.packet.cusp.count} (Rw : FC39P0.FC39RowsV2 W Et)
    (hEt : ∀ i, range (Et.torusMap i) = S.packet.cusp.component i) :
    ∃ G : RawGraphPresentation W, ∃ σ : Fin S.packet.cusp.count ≃ Fin G.externalCount,
      ∀ i, range (G.external.torusMap (σ i)) = S.packet.cusp.component i := by
  obtain ⟨_, ⟨⟨D, hD⟩⟩, -⟩ := boundary_graphPresentation_of_rows_BCF04 S Rw hEt
  exact exists_boundary_presentation_of_rimProduct_of_consumer
    (@fun W' _ _ _ D' h' => FC39P0.StrongCertificate.raw_or_aux_nonneg W' ⟨D', h'⟩) W
    S.packet.cusp D hD

end DifferentialGeometry.Geometry.Collapse
