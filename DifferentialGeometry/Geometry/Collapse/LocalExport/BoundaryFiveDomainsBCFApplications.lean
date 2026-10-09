import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFiveDomainsBCF

/-!
# Consumer of BCF03's first sentence (lane B-BCF134)

`BoundaryGaf02Chain.emptyDecomposition_five_domains_BCF03`: on BIFACE's empty-family decomposition
with the saturated empty cores, the five domains cover `W` and have pairwise disjoint interiors.
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

/-- **Consumer**: BCF03's first sentence on BIFACE's empty-family decomposition. -/
theorem emptyDecomposition_five_domains_BCF03 :
    (C.emptyInitialCores_BIF hz0).union ∪ C.cuspCores_BIF ∪
        (C.emptySlimChoice_BIF hc hF hz0).piece ∪ (C.emptySlimChoice_BIF hc hF hz0).edgePiece ∪
        (C.emptySlimChoice_BIF hc hF hz0).remainder = univ ∧
      Disjoint (interior ((C.emptyInitialCores_BIF hz0).union ∪ C.cuspCores_BIF))
        (interior (C.emptySlimChoice_BIF hc hF hz0).piece) ∧
      Disjoint (interior (C.emptySlimChoice_BIF hc hF hz0).edgePiece)
        (interior (C.emptySlimChoice_BIF hc hF hz0).remainder) :=
  ⟨(C.emptySlimChoice_BIF hc hF hz0).five_domains_cover_BCF03,
    (BoundaryCompactSlimChoice.five_domains_interiors_BCF03
      (Z := C.emptyInitialCoresSat_BCF hc hF hz0) (C.emptySlimChoice_BIF hc hF hz0)).1,
    (C.emptySlimChoice_BIF hc hF hz0).disjoint_interior_edgePiece_remainder_BCF03⟩

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
