import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdc04AtOCLFD4
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsNumerics74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFdc04CompleteFD4

/-!
# FDC04: the COMPLETE row at the produced cut choice `D_R` (G7)

Lane S-FDC04b (`_FD4`), group G7. On the closed source
`S : ClosedChainEZRowsSource_RGC K R M δ εr Λz` with its numerics record
`N : ClosedRowsNumericsAt74 S`, a bases object `B`, stage bases `A` and
the FDC facts `Htail` of the produced cut choice `D_R = S.goodCut_OCL B N.strategy_below N.eps_lt`:
`fdc04_row_complete_at_OCL_FD4` is `Gaf02ChainEJA.fdc04_row_complete_FD4` (G5: FDC04 row, the whole
EDP05 row with `edge_disk_in_face_EFE`, FC38's final row) for the production chain `S.chain` on the
final family `S.F.family` at `D_R` (`K₃, D₃` = ZSP04's chosen pair, admissible as in G4), together
with the FC39 cover field `CutCoverFacts74` of the produced stage geometry (G4). The FC38 numerics
(`β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`, `0 ≤ γ ≤ 3/4`) are the Gram request of S-REG-NUM
(`beta_two_le_RNUM`, `gamma_add_beta_lt_RNUM`) and the fields of `N`. `hK : 5 ≤ K`, `A` and `Htail`
are the explicit inputs of G4 as well.
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

/-- **FDC04's complete row on the production chain at `D_R`, and the FC39 cover field** (see the
module docstring). -/
theorem fdc04_row_complete_at_OCL_FD4 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S) (N : ClosedRowsNumericsAt74 S) (hK : 5 ≤ K) (A : SmoothStageBases74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt)) :
    type_of% (Gaf02ChainEJA.fdc04_row_complete_FD4 S.F.family S.chain A
      (R.beta_two_le_RNUM N.strategy_below) (R.gamma_add_beta_lt_RNUM N.strategy_below) N.eps_lt
      R.two_le_Δ_EDP23
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.1
      R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le R.qe_le_thousandth_OCL
      (R.b_mul_le_OCL N.strategy_below) N.gamma_nonneg N.gamma_le
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.2.2
      (S.chain.slimK₃_OCL N.eps_lt) (S.chain.slimD₃_OCL N.eps_lt)
      (S.chain.slimDomains_spec_OCL N.eps_lt).1 (S.chain.slimDomains_spec_OCL N.eps_lt).2.1
      (S.chain.slimDomains_spec_OCL N.eps_lt).2.2.1
      (S.goodCut_D₃_reg_OCL B N.strategy_below N.eps_lt)
      (S.goodCut_D₃_bdry_OCL B N.strategy_below N.eps_lt) hK
      (S.goodCut_hcpt_OCL B N.strategy_below N.eps_lt Htail)) ∧
    CutCoverFacts74 (S.closedStagesAt_OCL B N.strategy_below N.eps_lt A
        (S.zsp02SmoothExit74 N.eps_lt)).A
      (S.closedStagesAt_OCL B N.strategy_below N.eps_lt A (S.zsp02SmoothExit74 N.eps_lt)).cut :=
  ⟨Gaf02ChainEJA.fdc04_row_complete_FD4 S.F.family S.chain A
      (R.beta_two_le_RNUM N.strategy_below) (R.gamma_add_beta_lt_RNUM N.strategy_below) N.eps_lt
      R.two_le_Δ_EDP23
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.1
      R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le R.qe_le_thousandth_OCL
      (R.b_mul_le_OCL N.strategy_below) N.gamma_nonneg N.gamma_le
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.2.1
      (R.edpE_numerics_RGC N.strategy_below N.nb_eq N.cw_eq).2.2.2.2.2.2.2.2
      (S.chain.slimK₃_OCL N.eps_lt) (S.chain.slimD₃_OCL N.eps_lt)
      (S.chain.slimDomains_spec_OCL N.eps_lt).1 (S.chain.slimDomains_spec_OCL N.eps_lt).2.1
      (S.chain.slimDomains_spec_OCL N.eps_lt).2.2.1
      (S.goodCut_D₃_reg_OCL B N.strategy_below N.eps_lt)
      (S.goodCut_D₃_bdry_OCL B N.strategy_below N.eps_lt) hK
      (S.goodCut_hcpt_OCL B N.strategy_below N.eps_lt Htail),
    (S.fdc04_row_at_OCL_FD4 B N.strategy_below N.nb_eq N.cw_eq N.eps_lt hK A Htail).2⟩

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
