import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimFacesSatBCF

/-!
# Consumers of BCF01's interface pack and of G3 on the saturated cores (lane B-BCF134)

* `BoundaryActualDecomposition.bcf01_interface_BCF`: on the actual decomposition `dec` of a chain,
  `f₃` is continuous on `X₃`, `S` and `M₂` are compact, and the face inclusions
  `S ∩ M₂ ⊆ ∂S \ ∂M₁`, `∂M₁ \ S ⊆ ∂M₂`, `∂M₂ ⊆ (∂M₁ \ S) ∪ (∂S \ ∂M₁)` hold.
* `BoundaryGaf02Chain.emptyDecomposition_bcf01_BCF01`: on BIFACE's empty-family decomposition with
  the saturated empty cores, `S ⊆ M₁` and `S ∩ M₂ = ∂S \ ∂M₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
    δn n B oM}

/-- **Consumer**: BCF01's interface pack on the actual decomposition of a chain. -/
theorem BoundaryActualDecomposition.bcf01_interface_BCF {Φ : BoundaryInteriorSlots_BIF S}
    {D : BoundaryAugmentedData S Φ} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} (dec : BoundaryActualDecomposition C) :
    ContinuousOn (C.stageMap 2) (dec.bases.source 2) ∧ IsCompact dec.slim.piece ∧
      IsCompact dec.slim.M₂ ∧
      dec.slim.piece ∩ dec.slim.M₂ ⊆ frontier dec.slim.piece \ frontier dec.zero.M₁ ∧
      frontier dec.zero.M₁ \ dec.slim.piece ⊆ frontier dec.slim.M₂ ∧
      frontier dec.slim.M₂ ⊆ (frontier dec.zero.M₁ \ dec.slim.piece) ∪
        (frontier dec.slim.piece \ frontier dec.zero.M₁) :=
  ⟨dec.bases.continuousOn_stageMap_BCF 2, dec.slim.isCompact_piece_BCF, dec.slim.isCompact_M₂_BCF,
    dec.slim.piece_inter_M₂_subset_BCF, dec.slim.frontier_M₁_diff_subset_BCF,
    dec.slim.frontier_M₂_subset_BCF⟩

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
  {bcut bder κ : ℝ} (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)
  (hz0 : letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    S.family.zero.centres = ∅)

/-- **Consumer**: G3's first conjunct and `S ⊆ M₁` on BIFACE's empty-family decomposition with
the saturated empty cores. -/
theorem emptyDecomposition_bcf01_BCF01 :
    (C.emptySlimChoice_BIF hc hF hz0).piece ⊆ (C.emptyInitialCores_BIF hz0).M₁ ∧
      (C.emptySlimChoice_BIF hc hF hz0).piece ∩ (C.emptySlimChoice_BIF hc hF hz0).M₂ =
        frontier (C.emptySlimChoice_BIF hc hF hz0).piece \
          frontier (C.emptyInitialCores_BIF hz0).M₁ :=
  ⟨BoundaryCompactSlimChoice.piece_subset_M₁_BCF01 (Z := C.emptyInitialCoresSat_BCF hc hF hz0)
      (C.emptySlimChoice_BIF hc hF hz0),
    BoundaryCompactSlimChoice.piece_inter_M₂_eq_BCF01 (Z := C.emptyInitialCoresSat_BCF hc hF hz0)
      (C.emptySlimChoice_BIF hc hF hz0)⟩

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
