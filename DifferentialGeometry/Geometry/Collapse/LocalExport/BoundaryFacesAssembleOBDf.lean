import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFacesOBDf

/-!
# The face facts `JunctionFaceFacts74` of the rows over the produced stages (g1-g7)

Lane O-BD1 (by S-BD2f, suffix `_OBDf`), group G11k. Given the cover facts, the numerics of the
horizontal saturation and the end data of the slim pieces (`hfree`, `hend`: G10g), the rows over
the produced stages carry the whole structure of face facts:

* `edge_faces_rows_OBDf` (g3), `horizontalDisks_eq_OBDf` (the horizontal disks are
  `H_e = ∂M₂ ∩ X₂`), `region_boundary_rows_OBDf` (g5, `geom.pieces`);
* `exists_faces_OBDf`: the structure `JunctionFaceFacts74` (g1 g2 from G11i, g3, g4 g6 from G11h,
  g5, g7 from G11e).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section EdgeFaces

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **g3 `edge_faces`** for a label with whole disks. -/
theorem edge_faces_rows_OBDf {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (horizontal : R.edge.EdgeEnd → R.slimPieces.ResidualFace)
    (horizontal_disk : ∀ e, R.edge.disk e.1 ⊆ R.slimPieces.residualSet (horizontal e))
    (hfr : frontier P.cut.M₂ = R.slimPieces.boundaryM2)
    (hdisj : ∀ {Fl Fl' : R.slimPieces.ResidualFace}, Fl ≠ Fl' →
      Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl'))
    (Fl : R.slimPieces.ResidualFace) :
    P.cut.edgeSet ∩ R.slimPieces.residualSet Fl =
      ⋃ (e : R.edge.EdgeEnd) (_ : horizontal e = Fl), R.edge.disk e.1 :=
  R.edge_faces_of_OBDe horizontal horizontal_disk hfr
    (C.edgeSet_frontier_subset_disks_OBDf P R hrd hrd4 hrdc hprem hθ cov) hdisj Fl

include C in
/-- **The horizontal disks of the rows are the horizontal face `H_e = ∂M₂ ∩ X₂`.** -/
theorem horizontalDisks_eq_OBDf {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut) :
    R.edge.horizontalDisks = dec.slim.horizontalFace := by
  have hM2 : P.cut.M₂ = dec.slim.M₂ := (C.cut_M₂_M₃_eq_OBD P).1
  ext x
  constructor
  · intro hx
    obtain ⟨e, hxe⟩ := mem_iUnion.1 hx
    have hfrx := C.disk_subset_frontier_M₂_OBDe P R hrd hrd4 hrdc hprem hθ cov e hxe
    obtain ⟨z, ⟨-, hz2⟩, rfl⟩ := hxe
    exact ⟨hM2 ▸ hfrx, C.mem_source_one_of_edge_OBDe P R z hz2⟩
  · rintro ⟨hxfr, hx1⟩
    have hxM : x ∈ dec.slim.M₂ := (isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF
      dec.slim.piece).frontier_subset hxfr
    have hxE : x ∈ P.cut.edgeSet := by
      rw [C.cut_edgeSet_eq_OBD P]
      exact ⟨hxM, hx1⟩
    exact mem_iUnion.2 (C.edgeSet_frontier_subset_disks_OBDf P R hrd hrd4 hrdc hprem hθ cov x
      ⟨hxE, hM2 ▸ hxfr⟩)

include C in
/-- **g5 `region_boundary`** (from `geom.pieces` and `horizontalDisks = H_e`). -/
theorem region_boundary_rows_OBDf (geom : BoundaryGeometricExports74b C.toChain dec)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hfr : frontier P.cut.M₂ = R.slimPieces.boundaryM2) :
    P.cut.M₃ ∩ R.slimPieces.boundaryM2 =
      R.slimPieces.boundaryM2 \ relInt R.slimPieces.boundaryM2 R.edge.horizontalDisks := by
  rw [← hfr, C.horizontalDisks_eq_OBDf P R hrd hrd4 hrdc hprem hθ cov,
    (C.cut_M₂_M₃_eq_OBD P).2, (C.cut_M₂_M₃_eq_OBD P).1]
  exact geom.pieces.2.2.2.2.2.1

include C in
/-- **The face facts of the rows over the produced stages** (fields g1-g7), given the end data of
the slim pieces (`hfree`, `hend` of G10g). -/
theorem exists_faces_OBDf (geom : BoundaryGeometricExports74b C.toChain dec)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hfree : ∀ e : R.slimPieces.NewEnd, ∀ x ∈ R.slimPieces.endSet e.1,
      x ∉ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp))
    (hend : ∀ x ∈ P.cut.slimSet ∩ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp),
      ∃ e F', R.slimPieces.endKind e = some F' ∧ x ∈ R.slimPieces.endSet e) :
    Nonempty (JunctionFaceFacts74 P.stageGeometry P.cut R) := by
  have hfr := C.frontier_M₂_rows_OBDe P R geom cov hfree hend
  have hslim := C.slim_M2_rows_OBDe P R geom cov hfree
  have hNew : ∀ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 ⊆ P.cut.M₂ := by
    intro e x hx
    have : x ∈ P.cut.slimSet ∩ P.cut.M₂ := hslim ▸ mem_iUnion.2 ⟨e, hx⟩
    exact this.2
  have hdisj : ∀ {Fl Fl' : R.slimPieces.ResidualFace}, Fl ≠ Fl' →
      Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl') :=
    fun hne => C.residualSet_disjoint_rows_OBDe P R geom cov hNew hne
  obtain ⟨horizontal, hh⟩ := C.exists_horizontal_OBDe P R hrd hrd4 hrdc hprem hθ cov hfr hdisj
  exact ⟨{ horizontal := horizontal
           horizontal_disk := hh
           edge_faces := C.edge_faces_rows_OBDf P R hrd hrd4 hrdc hprem hθ cov horizontal hh hfr
             hdisj
           frontier_M2 := hfr
           region_boundary := C.region_boundary_rows_OBDf P R geom hrd hrd4 hrdc hprem hθ cov hfr
           slim_M2 := hslim
           shared_removed := C.shared_removed_rows_OBDe P R geom }⟩

end BoundaryGaf02ChainE

end EdgeFaces

end DifferentialGeometry.Geometry.Collapse
