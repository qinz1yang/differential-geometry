import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCutFactsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryEmbeddedOBD

/-!
# Consumer of the embedded stage geometry (lane S-BD2c, suffix `_OBD`), group G7f

For every zero / cusp exit the produced stage geometry has the three base inclusions smooth
embeddings and carries `EdgeCutFacts74` (`edgeCutFacts_OBD` consumes `ContMDiff P.ιedge`, here
`IsSmoothEmbedding.contMDiff` of the embedded edge inclusion).
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
/-- **The embedded stage geometry carries the edge cut facts**: for every zero / cusp exit there are
stages whose circle inclusion is a smooth embedding and whose restricted edge bundle exists. -/
theorem exists_stageGeometry_embedded_edgeFacts_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    ∃ P : BoundaryStageGeometry74b zc,
      IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)) ∞ P.ιcircle ∧ EdgeCutFacts74 P.stageGeometry P.cut := by
  obtain ⟨P, -, hιe, hιc⟩ := C.exists_stageGeometry74b_embedded_OBD dec geom hint zc
  exact ⟨P, hιc, C.edgeCutFacts_OBD P hιe.contMDiff geom⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
