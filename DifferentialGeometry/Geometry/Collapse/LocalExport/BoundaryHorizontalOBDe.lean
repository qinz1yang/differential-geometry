import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM2OBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHprimLabelsOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreSatBG4
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageHorizontalOBDe

/-!
# The horizontal label of an endpoint: fields g1 `horizontal` and g2 `horizontal_disk`

Lane O-BD1 (by S-BD2e, suffix `_OBDe`), group G11i. For rows `R` over the produced stages:

* `isPreconnected_disk_OBDe`: the disks of the restricted edge bundle are preconnected;
* `disk_subset_frontier_M₂_OBDe`: for an endpoint `e` of `C₂` the whole disk over `e` lies in
  `∂M₂` (a point of the disk is in `closure M₂ᶜ`, and `H_e = ∂M₂ ∩ X₂` is a union of whole edge
  fibres, `horizontalFace_saturated_BG4`);
* `exists_horizontal_OBDe`: given `∂M₂ = ⋃ residual faces` (g4) and the disjointness of the residual
  faces, a label `horizontal : EdgeEnd → ResidualFace` with `disk e ⊆ residualSet (horizontal e)`.
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

omit [ConnectedSpace W.Carrier] in
/-- **Every disk of an edge bundle is preconnected.** -/
theorem isPreconnected_disk_OBDe (P : EdgeBundle W) (c : P.Base) : IsPreconnected (P.disk c) := by
  obtain ⟨φ, hφ, hr⟩ := P.fibre_disk c
  have := closedCell_preconnectedSpace_BCF 2
  have h : IsPreconnected (range φ) := isPreconnected_range hφ.isEmbedding.continuous
  rw [hr] at h
  exact h

section Horizontal

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **A point of the edge source below the level lies in `X₂` of the decomposition.** -/
theorem mem_source_one_of_edge_OBDe (x : R.edge.source) (hx2 : R.edge.height x ≤ R.edge.level) :
    (x : W.Carrier) ∈ dec.bases.source 1 := by
  have hxe : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
  have hh : P.edge.height ⟨x, hxe⟩ = C.toChain.heightRatio (x : W.Carrier) := P.edge_height _
  have hlev : P.edge.level = 4 * Δ := P.edge_level
  have hT : C.toChain.heightRatio (x : W.Carrier) ≤ 4 * Δ := by
    have : P.edge.height ⟨x, hxe⟩ ≤ P.edge.level := hx2
    rwa [hh, hlev] at this
  rw [dec.bases.edge_source_eq]
  refine ⟨?_, hT⟩
  rw [mem_preimage, ← P.edge_ident.proj_eq ⟨x, hxe⟩]
  exact P.edge_range ⟨_, rfl⟩

include C in
/-- **The whole disk over an endpoint lies in `∂M₂`.** -/
theorem disk_subset_frontier_M₂_OBDe {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut) (e : R.edge.EdgeEnd) :
    R.edge.disk e.1 ⊆ frontier P.cut.M₂ := by
  obtain ⟨y, hyd, hycl⟩ := exists_disk_point_mem_closure_OBDe R
    (C.edge_M₂_subset_edgeSet_OBDe P R) e
  have hedge : R.edge.edgePiece = P.cut.edgeSet := P.cut.edgePiece_edgeBundle74 R.edgeFacts
  have hdiskM : R.edge.disk e.1 ⊆ P.cut.M₂ := by
    intro x hx
    obtain ⟨z, ⟨hz1, hz2⟩, rfl⟩ := hx
    apply cov.edgeSet_subset_M₂
    rw [← hedge]
    exact ⟨z, ⟨hz1 ▸ R.edge.frontier_cbase_subset e.2, hz2⟩, rfl⟩
  have hyfr : y ∈ frontier P.cut.M₂ := by
    refine ⟨subset_closure (hdiskM hyd), fun hint => ?_⟩
    rw [closure_compl] at hycl
    exact hycl hint
  obtain ⟨zy, ⟨hzy1, hzy2⟩, rfl⟩ := hyd
  have hy1 : (zy : W.Carrier) ∈ dec.bases.source 1 := C.mem_source_one_of_edge_OBDe P R zy hzy2
  have hM2 : P.cut.M₂ = dec.slim.M₂ := (C.cut_M₂_M₃_eq_OBD P).1
  have hH : (zy : W.Carrier) ∈ dec.slim.horizontalFace := by
    rw [hM2] at hyfr
    exact ⟨hyfr, hy1⟩
  intro x hx
  obtain ⟨z, ⟨hz1, hz2⟩, rfl⟩ := hx
  have hx1 : (z : W.Carrier) ∈ dec.bases.source 1 := C.mem_source_one_of_edge_OBDe P R z hz2
  have hf : C.toChain.stageMap 1 (z : W.Carrier) = C.toChain.stageMap 1 (zy : W.Carrier) := by
    have hze : (z : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ z.2
    have hzye : (zy : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ zy.2
    rw [← P.edge_ident.proj_eq ⟨z, hze⟩, ← P.edge_ident.proj_eq ⟨zy, hzye⟩]
    have : (R.edge.proj z).1 = (R.edge.proj zy).1 := by rw [hz1, hzy1]
    exact congrArg P.ιedge this
  have hfib : (z : W.Carrier) ∈ dec.bases.fibre 1 (C.toChain.stageMap 1 (zy : W.Carrier)) :=
    ⟨hx1, hf⟩
  have hHz := C.horizontalFace_saturated_BG4 dec.fibres dec.zero hrd hrd4 hrdc hprem hθ dec.slim
    (zy : W.Carrier) hH (z : W.Carrier) hfib
  rw [hM2]
  exact hHz.1

include C in
/-- **Fields g1 / g2: a label with `disk e ⊆ residualSet (horizontal e)`**, from g4 and the
disjointness of the residual faces. -/
theorem exists_horizontal_OBDe {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hfr : frontier P.cut.M₂ = R.slimPieces.boundaryM2)
    (hdisj : ∀ {Fl Fl' : R.slimPieces.ResidualFace}, Fl ≠ Fl' →
      Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl')) :
    ∃ horizontal : R.edge.EdgeEnd → R.slimPieces.ResidualFace,
      ∀ e, R.edge.disk e.1 ⊆ R.slimPieces.residualSet (horizontal e) := by
  classical
  have h : ∀ e : R.edge.EdgeEnd, ∃ Fl : R.slimPieces.ResidualFace,
      R.edge.disk e.1 ⊆ R.slimPieces.residualSet Fl := by
    intro e
    obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk e.1
    have hne : (R.edge.disk e.1).Nonempty := by
      have hmem : φ (closedCellCenter 2) ∈ range φ := ⟨_, rfl⟩
      rw [hφ] at hmem
      exact ⟨_, hmem⟩
    exact exists_face_of_preconnected_OBDe R.slimPieces (isPreconnected_disk_OBDe R.edge e.1) hne
      (by rw [← hfr]; exact C.disk_subset_frontier_M₂_OBDe P R hrd hrd4 hrdc hprem hθ cov e) hdisj
  choose horizontal hh using h
  exact ⟨horizontal, hh⟩

end BoundaryGaf02ChainE

end Horizontal

end DifferentialGeometry.Geometry.Collapse
