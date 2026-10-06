import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutFactsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceV2Corollaries
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageJunctions74

/-!
# The FDC04 cover facts of the produced cut (lane S-BD2, suffix `_OBD`), group G7d

Lane O-BD1 (by S-BD2), hlift, cut facts `H`: **`BoundaryGaf02ChainE.cutCover_OBD`** is
`CutCoverFacts74` for ANY stage geometry `P : BoundaryStageGeometry74b zc`: the cover
`W = Z ∪ C ∪ slimSet ∪ M₂` (set theory), the slim set lies in `M₁` (`S ⊆ M₁`: the saturation of
`M₁ ∩ X₃`, `slimSource_inter_preimage_BIF`), the edge set lies in `M₂` (`edgeSet = edgePiece`),
zero domains and cusp cores are disjoint (`cuspCore_disjoint_actualZeroDomain_BGR`, E4 premises).
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
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}

/-- `M₁` of the zero / cusp exit is the chain's `M₁`. -/
theorem regionM1_eq_OBD (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    regionM1 zc.zero zc.cusp = C.toChain.M₁_BIFc := by
  obtain ⟨σ, hσ⟩ := zc.zero_link
  have h1 : (⋃ i, range (zc.zero.piece i).map) = ⋃ k, C.toChain.actualZeroDomain_BIFc k := by
    rw [← σ.surjective.iUnion_comp (fun k => C.toChain.actualZeroDomain_BIFc k)]
    exact iUnion_congr fun i => (hσ i).1
  have h2 : (⋃ b, range (zc.cusp.piece b).map) = C.toChain.cuspCores_BIF :=
    iUnion_congr fun b => (zc.cusp_link b).1
  unfold regionM1 BoundaryGaf02Chain.M₁_BIFc
  rw [h1, h2]

include C in
/-- **`CutCoverFacts74` for the produced cut.** -/
theorem cutCover_OBD (P : BoundaryStageGeometry74b zc) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) : CutCoverFacts74 P.stageGeometry P.cut := by
  have hM1 := C.regionM1_eq_OBD zc
  have hS : P.cut.slimSet = dec.slim.piece :=
    (stageSetSrc_LND74 P.slim_ident P.cut.D₃).trans (by rw [P.cut_D₃]; rfl)
  have hE : P.cut.edgeSet = dec.slim.edgePiece :=
    (edgeSetSrc_of_stage_LND74 P.edge_ident P.edge_height P.edge_level).trans
      P.edgePiece_eq.symm
  have hM2 : P.cut.M₂ = dec.slim.M₂ := by
    unfold StageCutChoice74.M₂
    rw [hM1, hS]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext p
    simp only [mem_univ, iff_true]
    by_cases h1 : p ∈ interior ((⋃ i, range (zc.zero.piece i).map) ∪
        ⋃ b, range (zc.cusp.piece b).map)
    · exact Or.inl (Or.inl (interior_subset h1))
    · have hp1 : p ∈ regionM1 zc.zero zc.cusp := h1
      by_cases h2 : p ∈ P.cut.slimSet
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨hp1, fun hr => h2 (relInt_subset_JN74 hr)⟩
  · rw [hS, hM1]
    rintro x ⟨hxX, -, hxD⟩
    have hq : x ∈ dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' dec.bases.slimBaseDomain_BIFc :=
      ⟨hxX, hxD⟩
    rw [dec.zero.slimSource_inter_preimage_BIF] at hq
    exact hq.1
  · rw [hE, hM2]
    exact inter_subset_left
  · intro i b
    obtain ⟨σ, hσ⟩ := zc.zero_link
    have h1 := (hσ i).1
    have h2 := (zc.cusp_link b).1
    change Disjoint (range (zc.zero.piece i).map) (range (zc.cusp.piece b).map)
    rw [h1, h2]
    exact (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ b (σ i)).symm

include C in
/-- The slim set of the cut is the decomposition's slim piece. -/
theorem cut_slimSet_eq_OBD (P : BoundaryStageGeometry74b zc) :
    P.cut.slimSet = dec.slim.piece :=
  (stageSetSrc_LND74 P.slim_ident P.cut.D₃).trans (by rw [P.cut_D₃]; rfl)

include C in
/-- The edge set of the cut is the decomposition's edge piece. -/
theorem cut_edgeSet_eq_OBD (P : BoundaryStageGeometry74b zc) :
    P.cut.edgeSet = dec.slim.edgePiece :=
  (edgeSetSrc_of_stage_LND74 P.edge_ident P.edge_height P.edge_level).trans
    P.edgePiece_eq.symm

include C in
/-- `M₂` and `M₃` of the cut are the decomposition's `M₂` and remainder `R_c`. -/
theorem cut_M₂_M₃_eq_OBD (P : BoundaryStageGeometry74b zc) :
    P.cut.M₂ = dec.slim.M₂ ∧ P.cut.M₃ = dec.slim.remainder := by
  have hM2 : P.cut.M₂ = dec.slim.M₂ := by
    unfold StageCutChoice74.M₂
    rw [C.regionM1_eq_OBD zc, C.cut_slimSet_eq_OBD P]
    rfl
  refine ⟨hM2, ?_⟩
  unfold StageCutChoice74.M₃
  rw [hM2, C.cut_edgeSet_eq_OBD P]
  rfl

include C in
/-- **`CircleCutFacts74.saturation` for the produced cut**: `M₃ = q₀⁻¹(C₁)` (`R_c` is a union of
whole circle fibres, `geom.pieces`). -/
theorem cut_saturation_OBD (P : BoundaryStageGeometry74b zc)
    (geom : BoundaryGeometricExports74b C.toChain dec) : P.cut.M₃ = P.cut.circleRegion := by
  rw [(C.cut_M₂_M₃_eq_OBD P).2]
  have hsat : dec.slim.remainder = dec.bases.source 0 ∩
      C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder) :=
    geom.pieces.2.2.2.2.2.2.1
  have h1 : P.cut.circleRegion = dec.bases.source 0 ∩
      C.toChain.stageMap 0 ⁻¹' (P.ιcircle '' P.cut.C₁) :=
    stageSetSrc_LND74 P.circle_ident P.cut.C₁
  rw [h1, P.cut_C₁]
  exact hsat

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
