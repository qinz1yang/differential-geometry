import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimSmoothOBD

/-!
# The rim core of `JunctionRimFacts74` for the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G11a (hlift, `JunctionRimFacts74` without
`local_faces`): for the produced stages with embedded base inclusions and ANY edge / circle cut
facts `F`, `G` there are `rimBase` (smooth on `C₂`, `rim c = fibre (rimBase c)` on `C₂`) and the
equation `edgeSet ∩ M₃ = vertical` (`geom.pieces`: `P_e ∩ R_c = V_e`).
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


section RimCore

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

include C in
/-- **`edge_region` of the rim facts**: `M^edge ∩ M₃` is the vertical face of the edge bundle. -/
theorem edgeSet_inter_M₃_eq_vertical_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (F : EdgeCutFacts74 P.stageGeometry P.cut) :
    P.cut.edgeSet ∩ P.cut.M₃ = (edgeBundle74 P.stageGeometry P.cut F).vertical := by
  have hlev : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
  have h1 : P.cut.edgeSet ∩ P.cut.M₃ = dec.slim.verticalFace := by
    rw [C.cut_edgeSet_eq_OBD P, (C.cut_M₂_M₃_eq_OBD P).2]
    exact geom.pieces.2.2.2.2.1
  rw [h1]
  ext y
  constructor
  · rintro ⟨hyE, hyT⟩
    have hyE' : y ∈ P.cut.edgeSet := by rw [C.cut_edgeSet_eq_OBD P]; exact hyE
    obtain ⟨h, hc, hh⟩ := hyE'
    refine ⟨⟨y, P.edge.mem_restrictParent_of h (P.cut.C₂_sub hc)⟩, ⟨hc, ?_⟩, rfl⟩
    have h2 : P.edge.height ⟨y, h⟩ = C.toChain.heightRatio y := P.edge_height _
    change P.edge.height ⟨y, h⟩ = P.stageGeometry.edge.level
    rw [h2, hlev]
    exact hyT
  · rintro ⟨x, ⟨hc, hh⟩, rfl⟩
    have hxpar : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
    have h2 : P.edge.height ⟨x, hxpar⟩ = C.toChain.heightRatio (x : W.Carrier) := P.edge_height _
    have hhT : C.toChain.heightRatio (x : W.Carrier) = 4 * Δ := by
      have : P.edge.height ⟨x, hxpar⟩ = P.stageGeometry.edge.level := hh
      rw [← h2, this, hlev]
    refine ⟨?_, hhT⟩
    rw [← C.cut_edgeSet_eq_OBD P]
    exact ⟨hxpar, hc, by
      change P.edge.height ⟨x, hxpar⟩ ≤ P.stageGeometry.edge.level
      rw [h2, hhT, hlev]⟩

include C in
/-- **The rim core of `JunctionRimFacts74`**: `rimBase` smooth on `C₂` with `rim c = fibre (rimBase
c)` on `C₂`, and `edge_region`. -/
theorem exists_rimCore_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (F : EdgeCutFacts74 P.stageGeometry P.cut) (G : CircleCutFacts74 P.stageGeometry P.cut)
    (hιe : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (hιc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιcircle) :
    ∃ rimBase : (edgeBundle74 P.stageGeometry P.cut F).Base →
        (circleBundle74 P.stageGeometry P.cut G).Base,
      ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase (edgeBundle74 P.stageGeometry P.cut F).cbase ∧
      (∀ c' ∈ (edgeBundle74 P.stageGeometry P.cut F).cbase,
        (edgeBundle74 P.stageGeometry P.cut F).rim c' =
          (circleBundle74 P.stageGeometry P.cut G).fibre (rimBase c')) ∧
      P.cut.edgeSet ∩ P.cut.M₃ = (edgeBundle74 P.stageGeometry P.cut F).vertical := by
  obtain ⟨rimBase, hrim⟩ := C.exists_rimBase_OBD P geom F G
  exact ⟨rimBase, C.rimBase_contMDiffOn_OBD P geom F G hιe hιc rimBase hrim, hrim,
    C.edgeSet_inter_M₃_eq_vertical_OBD P geom F⟩

end BoundaryGaf02ChainE

end RimCore

end DifferentialGeometry.Geometry.Collapse
