import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcsBCF

/-!
# Consumers of BCF01 G1b, A4c-from-`WF` and the piece regularity (lane B-BCF134)

* `BoundaryActualDecompositionV2.slimStage_relOpen_dec_BCF`: A4c on every v2 decomposition (`dec.fibres`);
* `BoundaryActualDecompositionV2.slimPiece_regular_dec_BCF`: the arc-form slim piece of `dec` is regular
  as soon as `K₃ ∩ D₃` is regular in `B₃` (and the identity with `dec.slim.piece_regular`);
* `BoundaryGaf02Chain.emptySlimChartIntervals_arcs_BCF01`: G1b on the empty family (no interval, the
  empty atlas): the arc form exists with the same (empty) `K₃`.
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryActualDecompositionV2

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} (dec : BoundaryActualDecompositionV2 C)

/-- **Consumer (A4c)**: on every v2 decomposition, `f₃|X₃` is relatively open onto `B₃`. -/
theorem slimStage_relOpen_dec_BCF :
    ∀ U ⊆ dec.bases.source 2, IsOpen U → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)), IsOpen O ∧ O ∩ dec.bases.base 2 = C.stageMap 2 '' U :=
  dec.fibres.slimStage_relOpen_BCF

/-- **Consumer (piece regularity)**: the arc-form slim piece is regular when `K₃ ∩ D₃` is regular in
`B₃`; this agrees with the decomposition's own field. -/
theorem slimPiece_regular_dec_BCF
    (hreg : dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc ⊆
      closure (relInterior_BIF (dec.bases.base 2) (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc))) :
    closure (interior dec.slim.piece) = dec.slim.piece :=
  dec.zero.slimPiece_regular_BCF dec.fibres dec.slim.isCompact_K₃_BIFc
    (iUnion_subset fun k => dec.slim.arc_subset_base k) hreg

end BoundaryActualDecompositionV2

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **Consumer (G1b, empty family)**: the arc form of the empty chart-interval `K₃`. -/
theorem emptySlimChartIntervals_arcs_BCF01 :
    ∃ Kc : BoundaryCompactSlimChoiceV2 (C.emptyBasesV2_BIFc hc hF),
      Kc.K₃ = (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).K₃ ∧
      Kc.piece = (C.emptyBasesV2_BIFc hc hF).slimPieceOf_BIFc
        (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF)).K₃ :=
  exists_compactSlimChoiceV2_of_intervals_BCF01 (C.emptyWholeFiberSpecV2_BIFc hc hF)
    (C.emptySlimChartIntervals_BIFc hc hF (C.emptySlimAtlas_BIFc hc hF))

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
