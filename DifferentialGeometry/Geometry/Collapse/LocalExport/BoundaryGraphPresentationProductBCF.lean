import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0WholeProduct

/-!
# BCF04, the whole-product branch (lane B-BCF134)

Blueprint `master207B.tex`, BCF04 (B:9886–9965): "In the whole-product case, `M = T² × I` is itself
a circle bundle over an annulus; use its actual labeled boundary identification." Frozen target G9
of `docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` (T:464–471), stated
verbatim on the stored supply `S` and T3B's labelled whole-product branch
`S.LabelledWholeProduct_BIF` (no cores, no chain).

* `boundary_graphPresentation_of_product_BCF04` (G9): boundary tori `Et` numbered by the packet's
  cusp components, a decomposition certificate with the rim-product clause, and
  `range (Et.torusMap i) = S.packet.cusp.component i`; from FC39-P0's whole-product strong
  certificate (`exists_certificate_of_product_strong`) through the raw carrier identification
  `annulusCircleCarrierDiffeomorphTorusInterval` (FC42 B13).
* `BoundaryGeometricOutput.graphPresentation_of_product_BCF04`: the same conclusion read off the
  product constructor of the boundary route's geometric output.
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

/-- **BCF04, the whole-product branch** (frozen G9, verbatim): T3B's labelled whole product of the
stored supply gives boundary tori numbered by the packet's cusp components and a decomposition
certificate with the rim-product clause whose external tori are exactly those components. -/
theorem boundary_graphPresentation_of_product_BCF04 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b
    s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : S.LabelledWholeProduct_BIF) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  obtain ⟨-, -, -, D, -, -⟩ := h
  exact FC39P0.exists_certificate_of_product_strong S.packet.cusp
    (annulusCircleCarrierDiffeomorphTorusInterval.{0}.trans D)

/-- **The product constructor of the geometric output** gives BCF04's labelled certificate. -/
theorem BoundaryGeometricOutput.graphPresentation_of_product_BCF04
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
    {bcut bder κ : ℝ} {O : BoundaryGeometricOutput S Φ Kj Ξ Sg eg c cw bcut bder κ}
    {cert : S.LabelledWholeProduct_BIF} (_hO : O = .product cert) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i :=
  boundary_graphPresentation_of_product_BCF04 S cert

end DifferentialGeometry.Geometry.Collapse
