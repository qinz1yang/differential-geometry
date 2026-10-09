import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHprimJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSequenceHeadFCW

/-!
# Draft 74, FC39 gate 1A at `D_R`, final form: NO residual input

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 consumer (suffix `_JN74`). The gate with the slim exit
`slimExitAt3_OCL` (the chosen exit with the end classification), the faces (g1–g7), the rims
(local faces, `rimBase`), `hdesc`, `hrank` and the endpoint primitives `hprim` ALL produced:

* **`closed_rows_gate_final_OCL`**: `closed_rows_gate7_JN74` (G30) with `hprim := hprim_at_JN74`:
  from the numerics (`hNb`, `hcw`), the FDC facts `Htail` and `hK : 5 ≤ K` alone it gives rows
  linked at `D_R` with a strong certificate;
* `closed_rowsAt_all_final_JN74`: the local layer `hrowsAt` of the FCW layer at universe 0,
  unconditional (`closed_rowsAt_of_residuals_FCW` replaced).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
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
  (hεr : εr < 1 / 2)

/-- **FC39 gate 1A at `D_R`, final form**: no residual input beyond the numerics. -/
theorem closed_rows_gate_final_OCL (A : SmoothStageBases74 S) (hK : 5 ≤ K)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  S.closed_rows_gate7_JN74 B hT hεr A hK hNb hcw Htail (S.hprim_at_JN74 B hT hεr A hK hNb hcw Htail)

end At

end ClosedChainEZRowsSource_RGC

/-- **The local layer `hrowsAt` at universe 0, unconditional** (`K ≥ 5`): for every source,
numerics record, bases object and FDC facts at `D_R`, rows linked at `D_R`. -/
theorem closed_rowsAt_all_final_JN74 (K : ℕ) (hK : 5 ≤ K) :
    ∀ (T : ClosedThresholdsV4 (earlyDataSharedV4 K))
      (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) (W : CompactCarrier.{0})
      (g : SmoothRiemannianMetric W.model W.Carrier) (M : ClosedModel W g) (δ εr Λz : ℝ)
      (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (N : ClosedRowsNumericsAt74 S)
      (B : ClosedBases74 S),
      ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt) →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw := by
  intro T R W g M δ εr Λz S N B Htail
  obtain ⟨Rw, L, -⟩ := S.closed_rows_gate_final_OCL B N.strategy_below N.eps_lt S.smoothBases74 hK
    N.nb_eq N.cw_eq Htail
  exact ⟨Rw, L⟩

end DifferentialGeometry.Geometry.Collapse
