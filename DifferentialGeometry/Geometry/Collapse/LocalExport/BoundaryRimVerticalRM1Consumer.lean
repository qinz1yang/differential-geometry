import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimVerticalRM1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesRestBC2

/-!
# Consumer of G2 (lane S-RIM81): BCF02's `hG6` with `hV` and `hF` produced

`bcf02_pieces_of_rest_BC2` (S-BCF02) takes the four atomic inclusions `hX1`, `hV`, `hF`, `hsat`. On
the actual chain `hV` and `hF` are now theorems (`verticalFace_subset_remainder_RM1`,
`remainder_inter_frontier_subset_RM1`), so `hG6` needs only `hX1` (a theorem of S-BCF02:
`remainder_subset_source_BC2`) and `hsat`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF02's `hG6` from `hX1` and `hsat` alone** (`hV`, `hF` are `_RM1` theorems). -/
theorem bcf02_pieces_of_hX1_hsat_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (hX1 : Kc.remainder ⊆ Bs.source 0)
    (hsat : Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
      Kc.remainder) :
    Kc.remainder ⊆ Bs.source 0 ∧ Kc.edgePiece ∩ Kc.remainder = Kc.verticalFace ∧
      Kc.remainder ∩ frontier Kc.M₂ =
        frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
      Kc.remainder = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ∧
      ∀ p ∈ Kc.verticalFace ∩ Kc.horizontalFace, ∃! ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0 :=
  Kc.bcf02_pieces_of_rest_BC2 er hX1 (C.verticalFace_subset_remainder_RM1 WF Kc er)
    (C.remainder_inter_frontier_subset_RM1 WF Kc er) hsat

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
