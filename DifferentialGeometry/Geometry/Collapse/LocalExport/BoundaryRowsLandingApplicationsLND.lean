import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsLandingLND
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphPresentationRowsBCF

/-!
# Consumer of the boundary landing records: rows linked to `dec` give the labelled graph

Lane S-LANDING (`_LND74`), G3. The landing `boundary_rows_of_actual_decomposition74` produces
tori `Et` (labels = the packet's cusp components) and rows `Rw` with `BoundaryRowsLink C dec Et Rw`.
These feed FC42 form (b) (`exists_rawGraphPresentation_of_rows_BCF04`) with the SAME labels:
`boundary_labelled_graph_of_rowsLink_LND74` returns the circle-region identification of the link
(`R_c` of the decomposition) together with the labelled raw graph presentation whose external tori
are the packet's cusp components.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

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

/-- **Consumer of `BoundaryRowsLink`**: rows linked to the decomposition `dec` of the chain `C`,
on tori `Et` whose labels are the packet's cusp components, give the circle region `R_c` of `dec`
and the labelled raw graph presentation (FC42 form (b)) with the same labels. -/
theorem boundary_labelled_graph_of_rowsLink_LND74 {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b
    s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM}
    {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {dec : BoundaryActualDecompositionV2 C}
    {Et : BoundaryTori W S.packet.cusp.count} {Rw : FC39P0.FC39RowsV2 W Et}
    (L : BoundaryRowsLink C dec Et Rw)
    (hEt : ∀ i, range (Et.torusMap i) = S.packet.cusp.component i) :
    Rw.circle.region = dec.slim.remainder ∧
      ∃ G : RawGraphPresentation W, ∃ σ : Fin S.packet.cusp.count ≃ Fin G.externalCount,
        ∀ i, range (G.external.torusMap (σ i)) = S.packet.cusp.component i := by
  obtain ⟨ι, -, -, -, -, -, hreg⟩ := L.circle
  exact ⟨hreg, exists_rawGraphPresentation_of_rows_BCF04 S Rw hEt⟩

end DifferentialGeometry.Geometry.Collapse
