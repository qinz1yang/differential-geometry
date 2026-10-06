import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovalOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointOBDe

/-!
# Consumer of the removal property (lane S-BD2e, suffix `_OBDe`), group G11e

For ANY rows `R` over the produced stages: the field g7 `shared_removed` of `JunctionFaceFacts74`
(`shared_removed_OBDe` with `hKR_OBDe`) and the pairwise disjointness of the residual faces
(`residualSet_disjoint_OBDe`, needing only the cover facts and `hNew`: the new ends lie in `M₂`).
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

section RemovalConsumer

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **g7 `shared_removed` on the rows over the produced stages.** -/
theorem shared_removed_rows_OBDe (geom : BoundaryGeometricExports74b C.toChain dec) :
    ∀ σ : ActualSharedFace R.slimPieces, R.slimPieces.endSet σ.1 ⊆
      relInt (regionM1 P.stageGeometry.zero P.stageGeometry.cusp) P.cut.slimSet :=
  shared_removed_OBDe R (C.hKR_OBDe geom P)

include C in
/-- **Distinct residual faces of the rows over the produced stages are disjoint** (given that the
new ends lie in `M₂`, field g6 `⊇`). -/
theorem residualSet_disjoint_rows_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hNew : ∀ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 ⊆ P.cut.M₂)
    {Fl Fl' : R.slimPieces.ResidualFace} (hne : Fl ≠ Fl') :
    Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl') :=
  residualSet_disjoint_OBDe R cov (C.hKR_OBDe geom P) hNew hne

end BoundaryGaf02ChainE

end RemovalConsumer

end DifferentialGeometry.Geometry.Collapse
