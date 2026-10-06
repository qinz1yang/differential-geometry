import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExports74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExitsOfRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74

/-!
# D74-4 frozen heads, unconditional: the assembler `J1` plugged in

Lane S-LANDING (`_LND74`), G2c. With `J1 = rows_of_smooth_stage_geometry74` (lane S-JUNCTIONS)
the heads of `StaticRegisterV4ChainRowsOfExports74` lose their assembler argument:

* **`closed_rows_of_geometric_exports_at74 S B G : ∃ Rw, ClosedRowsLinkAt74 S B G.choice Rw`**;
* **`closed_rows_of_chain_outputs74 S B G : ∃ Rw, ClosedRowsLink S B Rw`**;
* **`closed_rows_of_rows74 S B N Htail Hrows`**: the closed route from the three development-stage
  records.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **D74-4 frozen head** `closed_rows_of_geometric_exports_at74`: rows linked to the actual
objects of the chain at the SAME cut choice `G.choice`. -/
theorem closed_rows_of_geometric_exports_at74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExports74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAt74 S B G.choice Rw :=
  closed_rows_of_geometric_exports_at74_of_assembler
    (fun A D H => rows_of_smooth_stage_geometry74 A D H) S B G

/-- **D74-4 frozen head** `closed_rows_of_chain_outputs74` (`∃ D` version). -/
theorem closed_rows_of_chain_outputs74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExports74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLink S B Rw :=
  closed_rows_of_chain_outputs74_of_assembler
    (fun A D H => rows_of_smooth_stage_geometry74 A D H) S B G

/-- **The closed route from the three development-stage records** (`N`, `Htail`, `Hrows`) with
`J1` plugged in. -/
theorem closed_rows_of_rows74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) (Htail : ClosedFdcMemberFacts74 S B)
    (Hrows : RemainingActualRowExits74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLink S B Rw :=
  closed_rows_of_rows74_of_assembler (fun A D H => rows_of_smooth_stage_geometry74 A D H) S B N
    Htail Hrows

end DifferentialGeometry.Geometry.Collapse
