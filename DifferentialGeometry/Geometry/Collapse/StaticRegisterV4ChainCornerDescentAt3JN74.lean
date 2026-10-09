import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLocalFacesAssemble3JN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGate6dJN74

/-!
# Draft 74, the corner descent `hdesc` at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G31 exit-3 copy of G27 (suffix `_JN74`). The input
`hdesc : ∀ e, CornerDescent74 faces.facts rims e` of the gate at `D_R` for the rows with exit
`slimExitAt3_OCL`: for every
endpoint `e`, `cornerDescent_ofFibreConst_JN74` (G18) with the whole-fibre patch
`exists_cornerPatch_JN74` (G19), the fibre constancy of `T` (`cornerT_fibreConst_at_JN74`, G19) and
of the face function of the label `F.horizontal e` (`hconstH_atExit3_JN74`, G24: zero faces and new
slim ends), and a point of the rim fibre (every circle fibre is non-empty, G23).
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

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **`CornerDescent74` at every endpoint of `D_R`** (exit `slimExitAt3_OCL`). -/
def cornerDescent_at3_JN74
    (Rw : StageCutRows74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut)
    (hRw : Rw = (S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final)
    (F : JunctionFaceFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut Rw)
    (G : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut Rw)
    (e : Rw.edge.EdgeEnd) : CornerDescent74 F G e :=
  let hN := exists_cornerPatch_JN74 F G e
  cornerDescent_ofFibreConst_JN74 F G e hN.choose hN.choose_spec.1 hN.choose_spec.2
    (fun x y hx hxy => S.cornerT_fibreConst_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) Rw x y
      (hN.choose_spec.2 x hx).1 (hN.choose_spec.2 y (by rw [hxy]; exact hx)).1 hxy)
    (fun x y hx hxy => by
      subst hRw
      exact S.hconstH_atExit3_JN74 B hT hεr A hK edge final (F.horizontal e) x y
        (hN.choose_spec.2 x hx).2 (hN.choose_spec.2 y (by rw [hxy]; exact hx)).2 hxy)
    (by
      obtain ⟨_, p, hp, rfl⟩ := Rw.fibre_nonempty_JN74 (G.rimBase e.1)
      exact ⟨p, hp⟩)

/-- **FC39 gate 1A at `D_R`, seventh form**: `closed_rows_gate6d_JN74` with the corner descent
`hdesc` produced; the residual inputs are the faces (g), the rims (h) and the corner rank data
(i, `hrank`). -/
theorem closed_rows_gate6e_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (faces : EDP05HorizontalExitU74 (S.stagesAtZ_OCL B hT hεr A)
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK))
      (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
      (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
        (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw)))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      ((S.stagesAtZ_OCL B hT hεr A).rows
        (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
          (S.slimExitAt3_OCL B hT hεr A hK))
        (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
        (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
          (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))))
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate6d_JN74 B hT hNb hcw hεr A Htail hK faces rims
    (fun e => S.cornerDescent_at3_JN74 B hT hεr A hK _ _ _ rfl faces.facts rims e) hrank

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
