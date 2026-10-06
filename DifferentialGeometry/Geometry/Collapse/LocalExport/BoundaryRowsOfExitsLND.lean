import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLandingExitsLND

/-!
# The boundary landing `boundary_rows_of_actual_decomposition74`, assembler as an argument

Lane S-LANDING (`_LND74`), G3b. Draft 74 §4.3 / D74-16: from the chain `C`, the decomposition
`dec`, the frozen exports `geom : BoundaryGeometricExports74 C dec` and the exits `X` in the
assembler's vocabulary, tori `Et` whose labels are the packet's cusp components and rows
`Rw : FC39RowsV2 W Et` with `BoundaryRowsLink C dec Et Rw`. The assembler `J1`
(`rows_of_smooth_stage_geometry74`) is the explicit argument `hJ1`; `geom` supplies the
saturation of `R_c` (the `pieces` clause of G6) that the circle fields need.
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

/-- **D74-16 landing, assembler as an explicit argument**: tori `Et` with the packet's labels and
rows `Rw` linked to the SAME decomposition. -/
theorem boundary_rows_of_actual_decomposition74_of_assembler {S : BoundarySupply K A β βd εN Λ w Δ
    σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM}
    {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
    {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (hJ1 : ∀ (E : BoundaryTori W S.packet.cusp.count) (Ag : SmoothStageGeometry74 W E)
      (Dc : StageCutChoice74 Ag), StageCutGeometry74 Ag Dc →
      ∃ Rw : FC39RowsV2 W E, StageRowsLink74 Ag Dc Rw)
    (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (dec : BoundaryActualDecompositionV2 C)
    (geom : BoundaryGeometricExports74 C dec) (X : BoundaryLandingExits74 C dec) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink C dec Et Rw := by
  obtain ⟨Rw, L⟩ := hJ1 X.zc.Et X.stages.stageGeometry X.stages.cut X.geometry
  refine ⟨X.zc.Et, X.zc.labels, Rw, ?_⟩
  have hz : ∃ σ : Fin Rw.zero.count ≃ S.ZeroIdx_BAUGC, ∀ k,
      range (Rw.zero.piece k).map = C.actualZeroDomain_BIFc (σ k) ∧
        Rw.zero.ratio k = dec.zero.defFn (σ k) := by
    rw [L.zeroSlim.zero_eq]
    exact X.zc.zero_link
  have hc : ∀ i, range (Rw.cusp.piece i).map = C.cuspCore_BIF i ∧
      (range fun t => (Rw.cusp.piece i).map (Rw.cusp.product i (t, iccEnd true))) =
        C.cuspFront_BIF i ∧
      ∀ x ∈ Rw.cusp.near i,
        Rw.cusp.cuspFn i x = chainBoundaryU_BCG6K C.E i x - 40 * chainBoundaryV_BCG6K C.E i x := by
    rw [L.zeroSlim.cusp_eq]
    exact X.zc.cusp_link
  have hslim := slimLinkSrc_of_stage_LND74 L.zeroSlim X.stages.slim_ident X.stages.cut_D₃
    X.stages.comp X.stages.comp_eq
  have hedge := edgeLinkSrc_of_stage_LND74 L.edge X.stages.edge_ident X.stages.edge_height
    X.stages.edge_level X.stages.edge_range dec.bases.parent.edgeParent_cut X.stages.cut_C₂
    X.stages.edgePiece_eq
  have hsat : dec.slim.remainder =
      dec.bases.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' dec.slim.remainder) :=
    geom.pieces.2.2.2.2.2.2.1
  have hcircle := circleLinkSrc_of_stage_LND74 L.circle X.stages.circle_ident
    X.stages.circle_range (remB := dec.slim.remainder) X.stages.cut_C₁
    (by rw [X.stages.cut_C₁]; exact hsat)
  have hM1 : regionM1 X.zc.zero X.zc.cusp = C.M₁_BIFc := by
    obtain ⟨σ, hσ⟩ := X.zc.zero_link
    have h1 : (⋃ i, range (X.zc.zero.piece i).map) = ⋃ k, C.actualZeroDomain_BIFc k := by
      rw [← σ.surjective.iUnion_comp (fun k => C.actualZeroDomain_BIFc k)]
      exact iUnion_congr fun i => (hσ i).1
    have h2 : (⋃ b, range (X.zc.cusp.piece b).map) = C.cuspCores_BIF :=
      iUnion_congr fun b => (X.zc.cusp_link b).1
    unfold regionM1 BoundaryGaf02Chain.M₁_BIFc
    rw [h1, h2]
  have hS : X.stages.cut.slimSet = dec.slim.piece :=
    (stageSetSrc_LND74 X.stages.slim_ident X.stages.cut.D₃).trans (by rw [X.stages.cut_D₃]; rfl)
  have hE : X.stages.cut.edgeSet = dec.slim.edgePiece :=
    (edgeSetSrc_of_stage_LND74 X.stages.edge_ident X.stages.edge_height X.stages.edge_level).trans
      X.stages.edgePiece_eq.symm
  have hreg := regionsLinkSrc_of_stage_LND74 L.regions hM1 hS hE (M₂c := dec.slim.M₂)
    (M₃c := dec.slim.remainder) rfl rfl
  exact ⟨hz, hc, hslim, hedge, hcircle, hreg.1, hreg.2.1, hreg.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
