import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutFactsOBD

/-!
# Consumer of the cut facts (lane S-BD2, suffix `_OBD`), group G7c

**`BoundaryGaf02ChainE.exists_stageGeometry_cutFacts_OBD`**: for every zero / cusp exit `zc` the
stage geometry of G7b exists with the four cut facts that need no further geometry: the properness
of the restricted circle and edge projections and the compactness of the circle and edge base
pieces `C₁`, `C₂` (the fields `proper`, `cbase_compact` of `CircleCutFacts74` / `EdgeCutFacts74`).
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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}


namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
theorem exists_stageGeometry_cutFacts_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    ∃ P : BoundaryStageGeometry74b zc,
      (∀ K : Set P.cut.circleBaseOpen, IsCompact K →
        IsCompact (Subtype.val ''
            (P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen ⁻¹' K))) ∧
      (∀ K : Set P.cut.edgeBaseOpen, IsCompact K →
        IsCompact (Subtype.val '' {x : P.cut.edgeSource |
          P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen x ∈ K ∧
            P.cut.edgeHeight x ≤ P.stageGeometry.edge.level})) ∧
      IsCompact (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) ∧
      IsCompact (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) := by
  obtain ⟨P⟩ := C.exists_stageGeometry74b_OBD dec geom hint zc
  exact ⟨P, P.circle_proper_OBD, P.edge_proper_OBD, C.circle_cbase_compact_OBD P geom,
    C.edge_cbase_compact_OBD P geom⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
