import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExitsAtOCL

/-!
# Draft 74 CL0, G4a: FDC04's cover of the produced stage geometry at `D_R`

Lane O-CL1 (`_OCL`), group G4a. On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` (G3a) at `D_R = S.goodCut_OCL B hT hεr`:

* the regions of the carried cut are the `M.ψ`-images of the actual regions of `D_R`:
  `zeroRanges_at_OCL` (`⋃ range (Z.piece i) = ψ(Z)`, from the zero exit's link),
  `regionM1_at_OCL` (`M₁ = ψ(M₁)`), `slimSet_at_OCL`, `M₂_at_OCL`, and, given EDP04's set
  equality (FDC02, the `edgeSet_eq` field of the edge exit), `edgeSet_at_OCL`;
* **`cover_at_OCL`**: `CutCoverFacts74 P.A P.cut` (FDC04's point-set cover
  `W = Z ∪ slimSet ∪ M₂`, `slimSet ⊆ M₁`, `M^edge ⊆ M₂`, zero / cusp disjointness: closed route,
  no cusp core), from O-CL0 G1's `goodCut_facts_OCL`, with NO further input than the zero exit and
  the edge exit's set equality;
* **`fdc03RemainderAt_OCL`**: the remainder exit `FDC03ActualRemainderU74 P` from the circle facts
  alone (the cover is produced).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The zero exit's pieces cover exactly `M.ψ(Z)`, `Z = ⋃_k Z_k` (ZSP03's removed region). -/
theorem zeroRanges_at_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (zero : ZSP02SmoothExit74 S) :
    ⋃ i, range (zero.rows.piece i).map = M.ψ '' S.chain.zeroUnion_ZSP35 := by
  obtain ⟨σ, hσ⟩ := zero.link
  have h : ∀ i, range (zero.rows.piece i).map = M.ψ '' S.zeroDom74 (σ i) := fun i => (hσ i).1
  simp only [h]
  rw [σ.surjective.iUnion_comp (fun k => M.ψ '' S.zeroDom74 k), ← image_iUnion]
  rfl

/-- `M₁` of the rows' zero domains (no cusp core) is `M.ψ(M₁)`, `M₁ = (int Z)ᶜ`. -/
theorem regionM1_at_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (zero : ZSP02SmoothExit74 S) :
    regionM1 zero.rows M.cusp_R74 = M.ψ '' S.chain.toGaf02ChainE.cutM1_R74 := by
  unfold regionM1
  simp only [iUnion_of_empty, union_empty]
  rw [S.zeroRanges_at_OCL zero, ← image_interior_R74 M.ψ, Gaf02ChainE.cutM1_R74]
  exact (image_compl_eq M.ψ.toEquiv.bijective).symm

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The slim set of the carried cut is `M.ψ` of the slim set of `D_R`. -/
theorem slimSet_at_OCL :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet =
      M.ψ '' (S.goodCut_OCL B hT hεr).slimSet :=
  slimSetW_of_stage_LND74 (S.closedStagesAt_OCL B hT hεr A zero).slim_ident
    (S.closedStagesAt_OCL B hT hεr A zero).cut_D₃

/-- `M₂` of the carried cut is `M.ψ` of `M₂` of `D_R`. -/
theorem M₂_at_OCL :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ := by
  change regionM1 zero.rows M.cusp_R74 \ relInt (regionM1 zero.rows M.cusp_R74)
    (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet = _
  rw [S.regionM1_at_OCL zero, S.slimSet_at_OCL B hT hεr A zero, relInt_image_R74 M.ψ,
    ← image_sdiff (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective, (S.goodCut_OCL B hT hεr).M₂_eq]
  rfl

/-- Given FDC02's set equality (the edge exit's `edgeSet_eq`), the edge set of the carried cut
is `M.ψ` of the edge set `M^edge` of `D_R`. -/
theorem edgeSet_at_OCL
    (hE : (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74})) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet =
      M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet := by
  rw [hE]
  exact edgeSetWU_of_stage_LND74 (S.closedStagesAt_OCL B hT hεr A zero).edge_ident
    (S.closedStagesAt_OCL B hT hεr A zero).edge_height
    (S.closedStagesAt_OCL B hT hεr A zero).edge_level
    (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂

/-- **FDC04's cover of the produced stage geometry at `D_R`** (`CutCoverFacts74`), from O-CL0 G1's
`goodCut_facts_OCL`, the zero exit's link and FDC02's set equality. -/
theorem cover_at_OCL
    (hE : (S.goodCut_OCL B hT hεr).edgeSet =
      gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
        (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' (S.goodCut_OCL B hT hεr).C₂ ∩
          {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74})) :
    CutCoverFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut := by
  have hF := S.goodCut_facts_OCL B hT hεr
  refine ⟨?_, ?_, ?_, fun _ b => b.elim0⟩
  · change ((⋃ i, range (zero.rows.piece i).map) ∪ ⋃ b, range (M.cusp_R74.piece b).map) ∪
      (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ∪
        (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ = univ
    simp only [iUnion_of_empty, union_empty]
    rw [S.zeroRanges_at_OCL zero, S.slimSet_at_OCL B hT hεr A zero, S.M₂_at_OCL B hT hεr A zero,
      ← image_union, ← image_union, hF.2.2.1]
    exact image_univ_of_surjective M.ψ.toEquiv.surjective
  · change (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ⊆ regionM1 zero.rows M.cusp_R74
    rw [S.slimSet_at_OCL B hT hεr A zero, S.regionM1_at_OCL zero, hF.1]
    exact image_mono inter_subset_left
  · rw [S.edgeSet_at_OCL B hT hεr A zero hE, S.M₂_at_OCL B hT hεr A zero]
    exact image_mono inter_subset_left

/-- **The remainder exit at `D_R` from the circle facts alone** (FDC04's cover produced). -/
def fdc03RemainderAt_OCL
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (facts : CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero) :=
  ⟨facts, S.cover_at_OCL B hT hεr A zero edge.edgeSet_eq⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
