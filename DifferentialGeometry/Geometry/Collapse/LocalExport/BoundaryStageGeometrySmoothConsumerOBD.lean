import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometrySmoothOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutCoverConsumerOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutFactsConsumerOBD

/-!
# Consumer of the smooth stage geometry (lane S-BD2, suffix `_OBD`), group G7e

**`BoundaryGaf02ChainE.exists_stageGeometry_smooth_facts_OBD`**: the stage geometry of G7b with
smooth edge inclusion (`exists_stageGeometry74b_smooth_OBD`) together with every cut fact proved
so far over it: the `proper` and `cbase_compact` fields of the circle and edge facts, the cover
facts and the circle saturation.
    (Every fact is stated for any `P`, so they apply to the smooth one.)
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
theorem exists_stageGeometry_smooth_facts_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ P : BoundaryStageGeometry74b zc,
      ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
        P.ιedge ∧
      Nonempty (CutCoverFacts74 P.stageGeometry P.cut) ∧ P.cut.M₃ = P.cut.circleRegion ∧
      (∀ K : Set P.cut.circleBaseOpen, IsCompact K →
        IsCompact (Subtype.val ''
            (P.stageGeometry.circle.restrictProj P.cut.circleBaseOpen ⁻¹' K))) ∧
      IsCompact (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) ∧
      IsCompact (Subtype.val ⁻¹' P.cut.C₂ : Set P.cut.edgeBaseOpen) := by
  obtain ⟨P, hι⟩ := C.exists_stageGeometry74b_smooth_OBD dec geom hint zc
  exact ⟨P, hι, ⟨C.cutCover_OBD P hrd hrd4 hrdc hprem hθ⟩, C.cut_saturation_OBD P geom,
    P.circle_proper_OBD, C.circle_cbase_compact_OBD P geom, C.edge_cbase_compact_OBD P geom⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
