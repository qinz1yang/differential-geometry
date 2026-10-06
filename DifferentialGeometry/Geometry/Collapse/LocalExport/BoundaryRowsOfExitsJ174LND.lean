import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfExitsLND
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsLandingApplicationsLND
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74

/-!
# The boundary landing, unconditional on the assembler: `J1` plugged in

Lane S-LANDING (`_LND74`), G3c. With `J1 = rows_of_smooth_stage_geometry74` (lane S-JUNCTIONS):

* **`boundary_rows_of_actual_decomposition74_of_exits C dec geom X`**: the landing of D74-16
  (tori with the packet's labels and rows linked to `dec`) from the chain `C` (the enhanced chain,
  through its plain chain `C.toChain`), the decomposition, the frozen exports and the exits;
* consumer **`boundary_graphPresentation_of_actual_decomposition_BCF04_of_exits`**: with G8b
  (`exists_strongCertificate_of_rows_GFIN`) the certificate with the rim-product clause on the SAME
  tori, whose range equations are the labels FC42 form (b) takes.
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

/-- **D74-16 landing from the exits** (assembler plugged in). -/
theorem boundary_rows_of_actual_decomposition74_of_exits {S : BoundarySupply K A β βd εN Λ w Δ σs σc
    μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM}
    {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (dec : BoundaryActualDecompositionV2 C)
    (geom : BoundaryGeometricExports74 C dec) (X : BoundaryLandingExits74 C dec) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink C dec Et Rw :=
  boundary_rows_of_actual_decomposition74_of_assembler
    (fun _ Ag Dc H => rows_of_smooth_stage_geometry74 Ag Dc H) C dec geom X

/-- **Consumer** (the frozen second head, composed): the landing's rows give the certificate with
the rim-product clause on tori whose range equations are the packet's labels. -/
theorem boundary_graphPresentation_of_actual_decomposition_BCF04_of_exits {S : BoundarySupply K A β
    βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM}
    {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (dec : BoundaryActualDecompositionV2 C)
    (geom : BoundaryGeometricExports74 C dec) (X : BoundaryLandingExits74 C dec) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      Nonempty {D : DecompositionCertificate W Et // D.RimProduct} ∧
        ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  obtain ⟨Et, hEt, Rw, L⟩ := boundary_rows_of_actual_decomposition74_of_exits C dec geom X
  exact boundary_graphPresentation_of_rows_BCF04 S Rw hEt

end DifferentialGeometry.Geometry.Collapse
