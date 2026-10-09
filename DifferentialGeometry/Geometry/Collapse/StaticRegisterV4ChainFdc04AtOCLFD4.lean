import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeSetEqOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCbaseDomainOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroExit74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFdc04RowFD4

/-!
# FDC04 at the produced cut choice `D_R`: the actual-chain row and the FC39 cover field

Lane S-FDC04 (`_FD4`), group G4. On the closed source
`S : ClosedChainEZRowsSource_RGC K R M δ εr Λz` and the produced cut choice
`D_R = S.goodCut_OCL B hT hεr` (its `K₃, D₃` are ZSP04's chosen pair, admissible:
`slimDomains_spec_OCL`, `goodCut_D₃_reg_OCL`, `goodCut_D₃_bdry_OCL`):

* **`fdc04_row_at_OCL_FD4`**: `Gaf02ChainEJA.fdc04_row_FD4` (zero pieces, slim pieces, four-piece
  cover with disjoint interiors, edge pieces, the FDC02 / EDP05 row, the horizontal disks) for the
  production chain `S.chain` at `D_R`. Its numeric premises are the register's (`edpE_numerics_RGC`
  and the `_OCL` numerics, exactly as in `goodCut_edge_disk_OCL`); `hcpt` is `goodCut_hcpt_OCL`
  (from FDC04's `edge_compact` in `Htail`, the D74-18 record `ClosedFdcFacts74`); `hK : 5 ≤ K` and
  the stage bases `A` are explicit inputs;
* **the FC39 field**: FDC04's cover as `CutCoverFacts74` of the produced stage geometry
  (`cover_at_OCL`, with FDC02's set equality `goodCut_edgeSet_eq_OCL` supplied here), the field of
  `StageCutGeometry74` that `cover_JN74` / `interiors_disjoint_JN74` turn into the `cover` /
  `interiors_disjoint` fields of `JunctionsV2`. The zero exit is `S.zsp02SmoothExit74 hεr`
  (clause (a) of the gate-1A table, produced by `StaticRegisterV4ChainZeroExit74`).
  NOT here: a register-level consumer (its `obtain` on the huge `type_of%` goal times out at 200000
  heartbeats; see state-S-FDC04.md).
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

/-- **FDC04's row on the production chain at `D_R`, and the FC39 cover field** (see the module
docstring). -/
theorem fdc04_row_at_OCL_FD4 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2) (hK : 5 ≤ K)
    (A : SmoothStageBases74 S) (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    type_of% (S.chain.fdc04_row_FD4 A hεr R.two_le_Δ_EDP23
      (R.edpE_numerics_RGC hT hNb hcw).2.2.1 (R.edpE_numerics_RGC hT hNb hcw).2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.1 (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.1
      R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT)
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.2.2
      (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr)
      (S.chain.slimDomains_spec_OCL hεr).1 (S.chain.slimDomains_spec_OCL hεr).2.1
      (S.chain.slimDomains_spec_OCL hεr).2.2.1 (S.goodCut_D₃_reg_OCL B hT hεr)
      (S.goodCut_D₃_bdry_OCL B hT hεr) hK (S.goodCut_hcpt_OCL B hT hεr Htail)) ∧
    CutCoverFacts74 (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).A
      (S.closedStagesAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)).cut :=
  ⟨S.chain.fdc04_row_FD4 A hεr R.two_le_Δ_EDP23
      (R.edpE_numerics_RGC hT hNb hcw).2.2.1 (R.edpE_numerics_RGC hT hNb hcw).2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.1 (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.1
      R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT)
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.2.1
      (R.edpE_numerics_RGC hT hNb hcw).2.2.2.2.2.2.2.2
      (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr)
      (S.chain.slimDomains_spec_OCL hεr).1 (S.chain.slimDomains_spec_OCL hεr).2.1
      (S.chain.slimDomains_spec_OCL hεr).2.2.1 (S.goodCut_D₃_reg_OCL B hT hεr)
      (S.goodCut_D₃_bdry_OCL B hT hεr) hK (S.goodCut_hcpt_OCL B hT hεr Htail),
    S.cover_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
      (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
