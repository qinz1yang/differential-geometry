import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesEndJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroLabelJN74

/-!
# Draft 74, the labels (fields g1, g2) of the face facts at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). On the rows with the exit
`slimExitAt3_OCL` (any edge and remainder exits): over every endpoint `e` of the edge base the whole
disk lies in ONE residual face: `label_at_JN74` (a zero label by `zero_label_at_JN74` (G22), a slim
label by `exists_newEnd_of_arcEnd_OCL` (S-REG-CHAIN6 G5): the free arc end is not a face point
because it lies in the relative interior of `C₃`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- The rows of the gate with the exit `slimExitAt3_OCL`, for any edge and remainder exits. -/
abbrev rows3_JN74 :
    StageCutRows74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut :=
  (S.stagesAtZ_OCL B hT hεr A).rows
    (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) (S.slimExitAt3_OCL B hT hεr A hK))
    edge final

/-- **The label of an endpoint: the whole disk lies in one residual face.** -/
theorem label_at_JN74 (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (e : (S.rows3_JN74 B hT hεr A hK edge final).edge.EdgeEnd) :
    ∃ Fl : (S.rows3_JN74 B hT hεr A hK edge final).slimPieces.ResidualFace,
      (S.rows3_JN74 B hT hεr A hK edge final).edge.disk e.1 ⊆
        (S.rows3_JN74 B hT hεr A hK edge final).slimPieces.residualSet Fl := by
  have hcases := S.edgeEnd_cases_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) Htail hNb hcw
    (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts e.1 e.2
  have hdisk : ∀ z, z ∈ (S.rows3_JN74 B hT hεr A hK edge final).edge.disk e.1 → ∃ y : M.X,
      S.chain.toGaf02ChainE.cutQ_R74 1 y =
        (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).ιedge e.1.1 ∧
        S.toE_RGC.toRowsSource_RGC.height y ≤
          (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).A.edge.level ∧
        M.ψ.toEquiv y = z := by
    intro z hz
    have hz' := (Set.ext_iff.1 (edgeBundle74_disk_eq_JN74
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).cut M.ψ.toEquiv
      (S.chain.toGaf02ChainE.cutQ_R74 1)
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).ιedge
      S.toE_RGC.toRowsSource_RGC.height
      (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).edge_ident.proj_eq
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).edge_ident.emb.injective
      (S.edge_parent_of_below_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr))
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).edge_height e.1) z).1 hz
    obtain ⟨y, ⟨h1, h2⟩, hy⟩ := hz'
    exact ⟨y, h1, h2, hy⟩
  rcases hcases with ⟨k, hk⟩ | ⟨k, b, hyC, hfree⟩
  · obtain ⟨i, Fm, hdiskF, hunsh⟩ := S.zero_label_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final) e k hk
    exact ⟨Sum.inl ⟨Sum.inl ⟨i, Fm⟩, hunsh⟩, hdiskF⟩
  · have hF3 : (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∉ S.chain.slimFacePoints_ZSP35 := by
      intro hF
      rw [← (S.chain.zsp03_slim_boundary_eq_ZSP35 hεr).2] at hF
      exact hF.2 hyC
    obtain ⟨en, -, -, hset⟩ := S.exists_newEnd_of_arcEnd_OCL B hT hεr A hK k b hF3
    refine ⟨Sum.inr en, fun z hz => ?_⟩
    obtain ⟨y, hq, hH, rfl⟩ := hdisk z hz
    have hmem : y ∈ S.chain.slimMap_ZSP35 ⁻¹' {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)} :=
      hfree y hq hH
    have hz2 : M.ψ y ∈ M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹'
        {(S.chain.slimD₃_OCL hεr).arc k (iccEnd b)}) := ⟨y, hmem, rfl⟩
    change M.ψ.toEquiv y ∈ (S.slimPieces3_JN74 B hT hεr A hK).endSet en.1
    rw [hset]
    exact hz2

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
