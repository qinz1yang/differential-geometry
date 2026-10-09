import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExportsU74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRank74

/-!
# D74-14 on the closed chain: the corner exit of EDP06 from descent and local rank data

Lane S-JUNCTIONS2 (`_JN74`), G6. The exit `EDP06CircleAgreementU74` of the revised closed landing
(`StaticRegisterV4ChainExportsU74`) is the rim facts `JunctionRimFacts74` together with the corner
facts `CornerCutFacts74` of every actual endpoint. This file produces the corner half from the two
pieces the chain rows will supply (D74-14, layers 1 and 2–4):

* `hdesc` — the descent patch at every endpoint (`CornerDescent74`: `T` and `h_F` pulled back from
  the circle base along `q₀`; NO row produces this yet);
* `hrank` — per endpoint the rank / sign / descended data (`CornerRank74`, `CornerDescended74`);
  `exists_cornerRank_descended_JN74` derives it from the descended face equation `b_e` (EDP05,
  `db_e ≠ 0`) and local sign neighbourhoods at the rim fibre (`rank` itself is DERIVED from EDP04's
  `rank_two`).

`EDP06CircleAgreementU74.ofCornerData` is the exit; `closed_strongCertificate_of_corner_data74` is
the end-to-end consumer (rows of the chain exits → junctions → labelled tubes → strong
certificate through `closed_strongCertificate_of_exportsU74`).
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

/-- **The EDP06 exit from the rim facts and the corner data.** -/
def EDP06CircleAgreementU74.ofCornerData {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    {P : ClosedStageGeometryU74 choice zero} {slim : ZSP04SmoothExitU74 P}
    {edge : EDP04WholeDiskExitU74 P} {final : FDC03ActualRemainderU74 P}
    (faces : EDP05HorizontalExitU74 P slim edge final)
    (rims : JunctionRimFacts74 P.A P.cut (P.rows slim edge final))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    EDP06CircleAgreementU74 P slim edge final faces :=
  ⟨rims, (exists_cornerCutFacts_JN74 hdesc hrank).some⟩

/-- **End-to-end consumer (D74-14 → J0 / J1 → GROUP G).** Exits of the closed chain up to the rim
facts, plus the descent patches and the per-endpoint rank data, give a strong certificate: the
corner exit of EDP06 is assembled, the geometry `H` is `ClosedStageGeometryU74.geometry`, the
rows come out of J1 and the certificate out of `exists_strongCertificate_of_rows_GFIN`. -/
theorem closed_strongCertificate_of_corner_data74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (choice : ClosedCutChoice74 S B) (zero : ZSP02SmoothExit74 S)
    (P : ClosedStageGeometryU74 choice zero) (slim : ZSP04SmoothExitU74 P)
    (edge : EDP04WholeDiskExitU74 P) (final : FDC03ActualRemainderU74 P)
    (faces : EDP05HorizontalExitU74 P slim edge final)
    (rims : JunctionRimFacts74 P.A P.cut (P.rows slim edge final))
    (hdesc : ∀ e, CornerDescent74 faces.facts rims e)
    (hrank : ∀ e, ∃ K : CornerRank74 faces.facts rims e, Nonempty (CornerDescended74 K)) :
    Nonempty (StrongCertificate W (BoundaryTori.empty W)) :=
  closed_strongCertificate_of_exportsU74 S B
    ⟨choice, zero, P, slim, edge, final, faces,
      EDP06CircleAgreementU74.ofCornerData faces rims hdesc hrank⟩

end DifferentialGeometry.Geometry.Collapse
