import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryNeighbourFrontierOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovalConsumerOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageNewEndOBDe

/-!
# Fields g4 `frontier_M2` and g6 `slim_M2` of the junction faces for the produced cut

Lane O-BD1 (by S-BD2e, suffix `_OBDe`), group G11h. On rows `R` over the produced stages, from the
removal property `hKR_OBDe`, `∂M₁` being the union of the neighbour faces, and the end data of the
slim exit (G10): the new ends miss `∂M₁` (`hfree`), and every point of `slimSet ∩ ∂M₁` lies in the
end set of a shared end (`hend`):

* `hfree_of_fibre_OBDe`: `hfree` from "the end set of a new end lies in the `f₃`-fibre over a
  value that is not a face value (`f₃(∂M₁ ∩ X₃)`)";
* `slim_M2_rows_OBDe`: `slimSet ∩ M₂ = ⋃ new ends` (g6);
* `frontier_M₂_rows_OBDe`: `∂M₂ = ⋃ residual faces` (g4).
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

section FrontierM2

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **The new ends miss `∂M₁`** when each lies in the `f₃`-fibre over a non-face value. -/
theorem hfree_of_fibre_OBDe
    (hexp : ∀ e : R.slimPieces.NewEnd, ∃ y : BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count),
      y ∉ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2) ∧
        R.slimPieces.endSet e.1 ⊆ dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) :
    ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp) := by
  intro e x hx hxf
  obtain ⟨y, hy, hsub⟩ := hexp e
  obtain ⟨hxX, hxy⟩ := hsub hx
  have hxf' : x ∈ frontier C.toChain.M₁_BIFc := by
    have h := C.regionM1_eq_OBD zc
    rw [← h]
    exact hxf
  exact hy ⟨x, ⟨hxf', hxX⟩, hxy⟩

include C in
/-- **Field g6 `slim_M2` on the rows over the produced stages.** -/
theorem slim_M2_rows_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hfree : ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp)) :
    P.cut.slimSet ∩ P.cut.M₂ = ⋃ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 :=
  slim_M2_OBDe R cov (C.hKR_OBDe geom P) hfree

include C in
/-- **Field g4 `frontier_M2` on the rows over the produced stages.** -/
theorem frontier_M₂_rows_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hfree : ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp))
    (hend : ∀ x ∈ P.cut.slimSet ∩ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp),
      ∃ e F', R.slimPieces.endKind e = some F' ∧ x ∈ R.slimPieces.endSet e) :
    frontier P.cut.M₂ = R.slimPieces.boundaryM2 :=
  frontier_M₂_OBDe R cov (C.hKR_OBDe geom P) hfree
    (hshare_of_ends_OBDe R cov (C.neighbourSet_subset_frontier_OBDe zc geom) hend)
    (C.neighbourSet_subset_frontier_OBDe zc geom) (C.frontier_subset_neighbours_OBDe zc geom)

end BoundaryGaf02ChainE

end FrontierM2

end DifferentialGeometry.Geometry.Collapse
