import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExports74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExports74

/-!
# D74-18: the development-stage records `N`, `Htail`, `Hrows` and the exports head

Lane S-LANDING (`_LND74`), G2b. Draft 74 §6.2: the exits of the closed route are produced from the
chain by existing theorems plus three DEVELOPMENT-STAGE records, removed item by item as the row
producers land (D74-18):

* `ClosedRowsNumericsAt74 S` (`N`): the register-layer numerics and strategy equalities the actual
  calls need (`ε_r < 1/2`, `σ_c ≤ 1/2`, `0 ≤ γ ≤ 3/4`, the (ZB) tolerance `e ≤ 1/1000`, and the
  premises `hT / hNb / hcw` of `edge_height_RGC`); their only consumer here is the cut-choice
  producer `exists_closedCutChoice74`;
* `ClosedFdcFacts74 S B D` / `ClosedFdcMemberFacts74 S B` (`Htail`): FDC04's conclusion on the
  ACTUAL sets of the member (compact edge piece and remainder, `M₂ = M^edge ∪ M₃`, the four-piece
  cover, pairwise disjoint interiors): the instance of `eventually_fdc04_cover_C14Z_FDC` at the
  current member, for every cut choice;
* `ClosedExitsOver74 S B choice` (the exits of `ClosedGeometricExports74` over a given choice) and
  `RemainingActualRowExits74 S B` (`Hrows`): the row-level exits not yet internalized, for every
  cut choice, GIVEN the FDC04 facts at it;
* **`closed_geometric_exports_of_rows74 S B N Htail Hrows`**:
  `Nonempty (ClosedGeometricExports74 S B)`;
* consumer `closed_rows_of_rows74_of_assembler`: with the assembler `hJ1`, the rows linked to the
  chain.
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

/-- **`N`: the numerics and strategy equalities of the actual calls** (D74-18). -/
structure ClosedRowsNumericsAt74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : Prop where
  eps_lt : εr < 1 / 2
  qe_le : R.later.err.co.qe ≤ 1 / 2
  gamma_nonneg : 0 ≤ R.later.circle.γ
  gamma_le : R.later.circle.γ ≤ 3 / 4
  e_le : R.later.err.co.e₀ ≤ 1 / 1000
  strategy_below : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  nb_eq : T.Nb = maxNb_V4C
  cw_eq : T.cw = maxCw_V4C

/-- **FDC04's conclusion on the actual sets of the member** at the cut choice `D`: the compact
edge piece and remainder, `M₂ = M^edge ∪ M₃`, the four-piece cover and the pairwise disjoint
interiors of `Z, Sl, M^edge, M₃`. -/
structure ClosedFdcFacts74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (D : ClosedCutChoice74 S B) : Prop where
  edge_compact : IsCompact D.edgeSet
  remainder_compact : IsCompact D.M₃
  M₂_eq : D.M₂ = D.edgeSet ∪ D.M₃
  cover : S.chain.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.edgeSet ∪ D.M₃ = univ
  zero_slim : Disjoint (interior S.chain.zeroUnion_ZSP35) (interior D.slimSet)
  zero_edge : Disjoint (interior S.chain.zeroUnion_ZSP35) (interior D.edgeSet)
  zero_remainder : Disjoint (interior S.chain.zeroUnion_ZSP35) (interior D.M₃)
  slim_edge : Disjoint (interior D.slimSet) (interior D.edgeSet)
  slim_remainder : Disjoint (interior D.slimSet) (interior D.M₃)
  edge_remainder : Disjoint (interior D.edgeSet) (interior D.M₃)

/-- **`Htail`: the FDC04 facts at the current member**, for every cut choice. -/
structure ClosedFdcMemberFacts74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S) : Prop where
  facts : ∀ D : ClosedCutChoice74 S B, ClosedFdcFacts74 D

/-- The exits of `ClosedGeometricExports74` over a given cut choice. -/
structure ClosedExitsOver74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (choice : ClosedCutChoice74 S B) where
  zero : ZSP02SmoothExit74 S
  stages : ClosedStageGeometry74 choice zero
  slim : ZSP04SmoothExit74 stages
  edge : EDP04WholeDiskExit74 stages
  final : FDC03ActualRemainder74 stages
  faces : EDP05HorizontalExit74 stages slim edge final
  rims : EDP06CircleAgreement74 stages slim edge final faces

/-- The exits over a choice, bundled with the choice. -/
def ClosedExitsOver74.toExports {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} (O : ClosedExitsOver74 choice) :
    ClosedGeometricExports74 S B :=
  ⟨choice, O.zero, O.stages, O.slim, O.edge, O.final, O.faces, O.rims⟩

/-- **`Hrows`: the row-level exits not yet internalized** (D74-18): for every cut choice, given
the FDC04 facts at it, the exits over it exist. Removed item by item as the producers land. -/
structure RemainingActualRowExits74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S) : Prop where
  exits : ∀ D : ClosedCutChoice74 S B, ClosedFdcFacts74 D → Nonempty (ClosedExitsOver74 D)

/-- **D74-18 head `closed_geometric_exports_of_rows74`**: the cut choice from the numerics `N`
(ZSP04's actual `K₃, D₃`, `exists_closedCutChoice74`), the FDC04 facts `Htail` at it, and the
remaining exits `Hrows` give the geometric exports on the SAME `(S, B)`. -/
theorem closed_geometric_exports_of_rows74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) (Htail : ClosedFdcMemberFacts74 S B)
    (Hrows : RemainingActualRowExits74 S B) : Nonempty (ClosedGeometricExports74 S B) := by
  obtain ⟨D, -⟩ := exists_closedCutChoice74 S B N.eps_lt N.qe_le N.gamma_nonneg N.gamma_le
  obtain ⟨O⟩ := Hrows.exits D (Htail.facts D)
  exact ⟨O.toExports⟩

/-- **Consumer: from the records to linked rows** (the closed route end to end modulo the three
development-stage records and the assembler): `N`, `Htail`, `Hrows` and `hJ1` give rows
`Rw : FC39RowsV2 W (BoundaryTori.empty W)` with `ClosedRowsLink S B Rw`. -/
theorem closed_rows_of_rows74_of_assembler {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) (Htail : ClosedFdcMemberFacts74 S B)
    (Hrows : RemainingActualRowExits74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLink S B Rw := by
  obtain ⟨G⟩ := closed_geometric_exports_of_rows74 S B N Htail Hrows
  exact closed_rows_of_chain_outputs74_of_assembler hJ1 S B G

end DifferentialGeometry.Geometry.Collapse
