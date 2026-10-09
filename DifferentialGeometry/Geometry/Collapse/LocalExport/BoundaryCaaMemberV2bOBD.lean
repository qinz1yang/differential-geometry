import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsHeadConsumerV2bOBD

/-!
# The CAA02 / BBR03 member conclusion from the boundary landing on v2b (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G6 (consumers). The per-sequence certificate binding
`hbseq` of `caa02_row_FCW` (and of BBR03's
`boundary_graph_threshold_of_sequence_binding_rimProduct_BQ`) asks, for every tail member
`(W, g, B)`, for tori `E : BoundaryTori W B.count` with a certificate with the rim-product
clause and `range (E.torusMap i) = B.component i`. The landing works on the supply's packet
labels (`S.packet.cusp`); the supply carries `S.cusp_eq : S.packet.cusp = B`.

* `caaMember_of_packetLabels_OBD S`: packet-labelled certificate ⟹ the member shape on `B`;
* **`BoundaryGaf02ChainE.caaMember_of_actual_decomposition74b_OBD`**: the BD2 head (G3) composed
  with BCF04 and the label transport — the member conclusion of `hbseq` for the member carrying
  the chain `C`, the decomposition `dec` with its exports `geom`, the Z1 cores and the stage lift.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

/-- **Label transport to the member's boundary**: a certificate with the rim-product clause on
tori labelled by the supply's packet components gives the CAA02 / BBR03 member shape on the
supplied boundary `B` (`S.cusp_eq : S.packet.cusp = B`). -/
theorem caaMember_of_packetLabels_OBD (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM)
    (h : ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i) :
    ∃ E : BoundaryTori W B.count, (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
      ∀ i, range (E.torusMap i) = B.component i := by
  rw [← S.cusp_eq]
  obtain ⟨Et, ⟨D, hD⟩, hEt⟩ := h
  exact ⟨Et, ⟨D, hD⟩, hEt⟩

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- **The CAA02 / BBR03 member conclusion from the boundary landing** (separated branch): the BD2
head on the v2b decomposition, BCF04, and the label transport. -/
theorem BoundaryGaf02ChainE.caaMember_of_actual_decomposition74b_OBD
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ E : BoundaryTori W B.count, (∃ Dc : DecompositionCertificate W E, Dc.RimProduct) ∧
      ∀ i, range (E.torusMap i) = B.component i :=
  caaMember_of_packetLabels_OBD S
    (C.boundary_graphPresentation_of_actual_decomposition74b_OBD dec geom Q hrd hrd4 hrdc hprem hθ
      hlift)

end DifferentialGeometry.Geometry.Collapse
