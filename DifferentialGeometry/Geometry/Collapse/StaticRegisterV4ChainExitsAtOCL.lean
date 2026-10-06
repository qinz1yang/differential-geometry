import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainStagesCutOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExportsU74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74

/-!
# Draft 74 CL0 / CL1, G3b: all exits at the produced cut choice `D_R`, one record

Lane O-CL1 (`_OCL`, successor of O-CL0), group G3b. At the produced cut choice
`D_R = S.goodCut_OCL B hT hεr` (O-CL0 G1) and the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` (G3a):

* **`exitsAt_OCL`**: the revised exits record `ClosedExitsOverU74 D_R` (S-LANDING G2d) with the
  stage geometry PRODUCED (`P`) and the row exits of the SAME `P` (`ZSP04SmoothExitU74 P`,
  `EDP04WholeDiskExitU74 P`, `FDC03ActualRemainderU74 P`, `EDP05HorizontalExitU74`,
  `EDP06CircleAgreementU74`) as explicit arguments, stated at `D_R` only (lead decision 21:15);
* **`zsp04ExitAt_OCL`**: the slim exit from S-JUNCTIONS G4's `SlimExit74` on `P`
  (`slimCutPieces_of_exit74`: arcs and loops, whole `f₃`-preimages, shared ends);
* **`remainingActualRowExitsU74_at_OCL`**: `Hrows` at `D_R`
  (`RemainingActualRowExitsU74 S B D_R`) from the same arguments;
* CL1 at `D_R`: **`closed_rows_at_OCL`** (`∃ Rw : FC39RowsV2 W ∅, ClosedRowsLinkAtU74 S B D_R Rw`),
  **`closed_rows_of_chain_outputs_OCL`** (`∃ D` form `ClosedRowsLinkU74 S B Rw`) and the certificate
  **`closed_strongCertificate_at_OCL`** (`exists_strongCertificate_of_rows_GFIN`), with `J1`
  (`rows_of_smooth_stage_geometry74`) plugged in.

The residual arguments are the open producers of the closed route (see `state-O-CL0.md`, section
O-CL1): the zero exit (Z2 with the selected cores `Q`, G27b), the slim exit binding to S-ZSP04's
arcs / loops, the edge facts (rank two, the `ψ`-transport of EDP04's whole disks, FDC02's domain
data), the edge component models (E3 / E4), the circle facts (C0 / FDC03 saturation), FDC04's
cover, and the EDP05 / EDP06 junction facts.
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
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **The slim exit at `D_R`** from S-JUNCTIONS G4's exits of the slim pieces on the produced
stage geometry (arcs and loops; each piece the whole `f₃`-preimage of its component of `D₃`). -/
def zsp04ExitAt_OCL
    (X : SlimExit74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero) :=
  ⟨slimCutPieces_of_exit74 X⟩

/-- **CL0 at `D_R`, one record**: the revised exits over the produced cut choice `D_R`, with the
stage geometry produced (`closedStagesAt_OCL`) and the row exits of that SAME stage geometry. -/
def exitsAt_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    ClosedExitsOverU74 (S.goodCut_OCL B hT hεr) where
  zero := zero
  stages := S.closedStagesAt_OCL B hT hεr A zero
  slim := slim
  edge := edge
  final := final
  faces := faces
  rims := rims

/-- The record's stage geometry is the produced one. -/
theorem exitsAt_stages_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    (S.exitsAt_OCL B hT hεr A zero slim edge final faces rims).stages =
      S.closedStagesAt_OCL B hT hεr A zero :=
  rfl

/-- **`Hrows` at `D_R`** (`RemainingActualRowExitsU74 S B D_R`) from the row exits on the produced
stage geometry. -/
theorem remainingActualRowExitsU74_at_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    RemainingActualRowExitsU74 S B (S.goodCut_OCL B hT hεr) :=
  ⟨fun _ => ⟨S.exitsAt_OCL B hT hεr A zero slim edge final faces rims⟩⟩

/-- **CL1 at `D_R`**: rows `Rw : FC39RowsV2 W ∅` linked (revised table) to the actual objects of
the chain at the produced cut choice `D_R` (assembler `J1` plugged in). -/
theorem closed_rows_at_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw :=
  closed_rows_of_geometric_exports_atU74 S B
    (S.exitsAt_OCL B hT hεr A zero slim edge final faces rims).toExports

/-- **CL1 (`closed_rows_of_chain_outputs74`, revised) at the produced `D_R`**: the `∃ D` form. -/
theorem closed_rows_of_chain_outputs_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkU74 S B Rw := by
  obtain ⟨Rw, L⟩ := S.closed_rows_at_OCL B hT hεr A zero slim edge final faces rims
  exact ⟨Rw, S.goodCut_OCL B hT hεr, L⟩

/-- **FC39 gate 1A at `D_R`**: GROUP G's strong certificate from the rows of the chain
(`exists_strongCertificate_of_rows_GFIN`). -/
theorem closed_strongCertificate_at_OCL
    (slim : ZSP04SmoothExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (edge : EDP04WholeDiskExitU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (final : FDC03ActualRemainderU74 (S.closedStagesAt_OCL B hT hεr A zero))
    (faces : EDP05HorizontalExitU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final)
    (rims : EDP06CircleAgreementU74 (S.closedStagesAt_OCL B hT hεr A zero) slim edge final
      faces) :
    Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, -⟩ := S.closed_rows_at_OCL B hT hεr A zero slim edge final faces rims
  exact exists_strongCertificate_of_rows_GFIN Rw

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
