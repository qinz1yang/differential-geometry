import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryNewEndOBDe

/-!
# Consumer: the rim facts and the corner facts together (lane S-BD2e, suffix `_OBDe`), group G11g

For rows `R` over the produced stages with face facts `F` and the `rel3` clause of the slim exit for
the new ends: rim facts `G` and corner facts `CornerCutFacts74 F G`, i.e. the last two fields of the
cut geometry `H` (`BoundaryLandingExits74b.rims` / `.corners`) from the face facts alone.
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

section RimsCorners

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **Rims and corners from the face facts.** -/
theorem exists_rimsCorners_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιedge)
    (hιc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιcircle)
    (hnew : ∀ en : R.slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) :
    ∃ G : JunctionRimFacts74 P.stageGeometry P.cut R, Nonempty (CornerCutFacts74 F G) := by
  obtain ⟨G⟩ := C.exists_rims_OBDe P R geom cov hι hιc hnew F
  exact ⟨G, C.exists_cornerCutFacts_OBDe P R geom cov hι.contMDiff hnew F G⟩

end BoundaryGaf02ChainE

end RimsCorners

end DifferentialGeometry.Geometry.Collapse
