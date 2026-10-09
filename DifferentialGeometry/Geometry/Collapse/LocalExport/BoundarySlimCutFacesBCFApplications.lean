import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutFacesBCF

/-!
# Consumers of BCF01 G0 / G3 on the v2 objects (lane B-BCF134)

* `BoundaryActualDecompositionV2.bcf01_faces_slim_BCF01`: for EVERY v2 decomposition, the three face
  identities at its arc-form `K₃` (`slimCut_BIFc`) and the absence of closed slim components of its
  base (`dec.fibres`), the G1 input that removes the shared kernel's loops on the boundary route.
* `BoundaryGaf02Chain.emptyDecompositionV2_faces_BCF01`: the same on the empty-family decomposition,
  together with G3 at the empty cut.
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

/-- **Consumer (every v2 decomposition)**: BCF01's three face identities at the arc-form `K₃`, and no
nonempty compact relatively open subset of the slim base. -/
theorem BoundaryActualDecompositionV2.bcf01_faces_slim_BCF01 {Φ : BoundaryInteriorSlots_BIF S}
    {D : BoundaryAugmentedData S Φ} {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    (dec : BoundaryActualDecompositionV2 C) :
    (dec.bases.slimPieceOf_BIFc dec.slim.K₃ ∩ dec.bases.M₂Of_BIFc dec.slim.K₃ =
        frontier (dec.bases.slimPieceOf_BIFc dec.slim.K₃) \ frontier C.M₁_BIFc ∧
      frontier (dec.bases.M₂Of_BIFc dec.slim.K₃) =
        (frontier C.M₁_BIFc \ dec.bases.slimPieceOf_BIFc dec.slim.K₃) ∪
          (frontier (dec.bases.slimPieceOf_BIFc dec.slim.K₃) \ frontier C.M₁_BIFc) ∧
      Disjoint (frontier C.M₁_BIFc \ dec.bases.slimPieceOf_BIFc dec.slim.K₃)
        (frontier (dec.bases.slimPieceOf_BIFc dec.slim.K₃) \ frontier C.M₁_BIFc)) ∧
    ∀ Y ⊆ dec.bases.base 2, IsCompact Y → Y.Nonempty →
      ¬ ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
        IsOpen O ∧ O ∩ dec.bases.base 2 = Y :=
  ⟨bcf01_faces_BCF01 dec.zero dec.slim.slimCut_BIFc, fun _ hY hYc hYne =>
    dec.bases.no_closed_slimBase_component_BCF01 dec.fibres hY hYc hYne⟩

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **Consumer (empty family)**: G3 at the empty slim cut of the empty v2 bases. -/
theorem emptyDecompositionV2_faces_BCF01
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    (C.emptyBasesV2_BIFc hc hF).slimPieceOf_BIFc ∅ ∩ (C.emptyBasesV2_BIFc hc hF).M₂Of_BIFc ∅ =
      frontier ((C.emptyBasesV2_BIFc hc hF).slimPieceOf_BIFc ∅) \ frontier C.M₁_BIFc :=
  (bcf01_faces_BCF01 (C.emptyActualZeroDomains_BIFc hc hF hz0) (C.emptySlimCut_BIFc hc hF)).1

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
