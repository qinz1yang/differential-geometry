import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesLabelJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSharedRemovedJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointJN74

/-!
# Draft 74, the face facts `JunctionFaceFacts74` at `D_R` (exit `slimExitAt3_OCL`)

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). The input `faces` of the gate at `D_R`,
PRODUCED:

* `edgeSet_frontier_subset_disks_JN74`: `M^edge ∩ ∂M₂` lies in the union of the horizontal disks
  (`edge_edgeSet_frontier_EFE` through `horizontalDisks_at_JN74`);
* `faces3_JN74`: g1, g2 (`label_at_JN74`), g3 (`edge_faces_of_JN74` from g4, the disks and the
  disjointness `residualSet_disjoint_JN74` with `hKR` from `zeroFace_slim_relInt_at_JN74` and
  `hNew` from `newEnd_subset_M₂_at_JN74`), g4 (`frontier_M₂_at_JN74`), g5
  (`region_boundary_at_JN74`), g6 (`slim_M₂_at_JN74`), g7 (`shared_removed_at_JN74`).
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
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **`M^edge ∩ ∂M₂ ⊆` the horizontal disks of the rows** (any edge facts). -/
theorem edgeSet_frontier_subset_disks_JN74 (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet ∩
        frontier (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ ⊆
      (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).horizontalDisks := by
  rw [S.horizontalDisks_at_JN74 B hT hεr A zero Htail F hNb hcw]
  rintro x ⟨hxE, hxM⟩
  rw [S.edgeSet_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)] at hxE
  rw [S.M₂_at_OCL B hT hεr A zero, ← image_frontier_R74 M.ψ] at hxM
  obtain ⟨y, hyE, rfl⟩ := hxE
  obtain ⟨y', hy'M, hyy'⟩ := hxM
  have hy : y' = y := M.ψ.injective hyy'
  subst hy
  obtain ⟨hyT, hysrc⟩ := S.chain.cutEdgeSet_height_le_JN74 R.two_le_Δ_EDP23
    (S.goodCut_OCL B hT hεr).K₃ hyE
  exact ⟨y', ⟨hy'M, ⟨y', hysrc⟩, hyT, rfl⟩, rfl⟩

variable (hK : 5 ≤ K) (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **The face facts of the rows at `D_R` with the exit `slimExitAt3_OCL`, produced** (the input
`faces` of the gate, for any edge and remainder exits): fields g1–g7. -/
def faces3_JN74 (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr) (S.slimExitAt3_OCL B hT hεr A hK))
      edge final :=
  ⟨S.junctionFaceFacts_ofPrimitives_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) Htail hNb hcw
    (S.rows3_JN74 B hT hεr A hK edge final)
    (fun e => Classical.choose (S.label_at_JN74 B hT hεr A hK edge final Htail hNb hcw e))
    (fun e => Classical.choose_spec (S.label_at_JN74 B hT hεr A hK edge final Htail hNb hcw e))
    (fun Fl => StageCutRows74.edge_faces_of_JN74 (S.rows3_JN74 B hT hεr A hK edge final) _
      (fun e => Classical.choose_spec (S.label_at_JN74 B hT hεr A hK edge final Htail hNb hcw e))
      (S.frontier_M₂_at_JN74 B hT hεr A hK)
      (fun x hx => by
        obtain ⟨e, he⟩ := mem_iUnion.1 (S.edgeSet_frontier_subset_disks_JN74 B hT hεr A
          (S.zsp02SmoothExit74 hεr) Htail (S.rows3_JN74 B hT hεr A hK edge final).edgeFacts hNb
          hcw hx)
        exact ⟨e, he⟩)
      (fun hne => residualSet_disjoint_JN74 (S.rows3_JN74 B hT hεr A hK edge final)
        (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr))
        (S.newEnd_subset_M₂_at_JN74 B hT hεr A hK) hne) Fl)
    (S.frontier_M₂_at_JN74 B hT hεr A hK) (S.slim_M₂_at_JN74 B hT hεr A hK)
    (S.shared_removed_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.rows3_JN74 B hT hεr A hK edge final))⟩

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
